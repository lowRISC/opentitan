// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash Phy Core Module
//
//
// This module wraps every single flash bank and contains most of the region attribute,
// scramble, ECC, security and arbitration logic.

module flash_phy_core
  import flash_phy_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter int unsigned ArbCnt = 4,
  parameter bit SecScrambleEn = 1'b1
) (
  input                              clk_i,
  input                              rst_ni,
  input                              host_req_i,   // host request - read only
  input                              host_scramble_en_i,
  input                              host_ecc_en_i,
  input [BusBankAddrW-1:0]           host_addr_i,
  input                              req_i,        // controller request
  input                              scramble_en_i,
  input                              ecc_en_i,
  input                              he_en_i,
  input                              rd_i,
  input                              prog_i,
  input                              pg_erase_i,
  input                              bk_erase_i,
  input                              erase_suspend_req_i,
  input flash_ctrl_pkg::flash_part_e part_i,
  input [InfoTypesWidth-1:0]         info_sel_i,
  input [BusBankAddrW-1:0]           addr_i,
  input [BusFullWidth-1:0]           prog_data_i,
  input                              prog_last_i,
  input flash_ctrl_pkg::flash_prog_e prog_type_i,
  input [KeySize-1:0]                addr_key_i,
  input [KeySize-1:0]                data_key_i,
  input [KeySize-1:0]                rand_addr_key_i,
  input [KeySize-1:0]                rand_data_key_i,
  input                              rd_buf_en_i,
  input prim_mubi_pkg::mubi4_t       flash_disable_i,
  input  flash_phy_prim_flash_rsp_t  prim_flash_rsp_i,
  output flash_phy_prim_flash_req_t  prim_flash_req_o,
  output logic                       host_req_rdy_o,
  output logic                       host_req_done_o,
  output logic                       rd_done_o,
  output logic                       prog_done_o,
  output logic                       erase_done_o,
  output logic [BusFullWidth-1:0]    rd_data_o,
  output logic                       rd_err_o,
  output logic                       ecc_single_err_o,
  output logic [BusBankAddrW-1:0]    ecc_addr_o,
  output logic                       fsm_err_o,
  output logic                       prog_intg_err_o,
  output logic                       relbl_ecc_err_o,
  output logic                       intg_ecc_err_o,
  output logic                       spurious_ack_o
);


  localparam int CntWidth = $clog2(ArbCnt + 1);

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 5 -m 6 -n 10 \
  //      -s 3884146959 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: --
  //  4: --
  //  5: |||||||||||||||||||| (46.67%)
  //  6: ||||||||||||||||| (40.00%)
  //  7: ||||| (13.33%)
  //  8: --
  //  9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 7
  // Minimum Hamming weight: 4
  // Maximum Hamming weight: 8
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    StIdle     = 10'b1011011110,
    StCtrlRead = 10'b0010100110,
    StCtrlProg = 10'b1111101101,
    StCtrl     = 10'b1101000010,
    StDisable  = 10'b0000111011,
    StInvalid  = 10'b0101110100
  } state_e;

  state_e state_q, state_d;

  // request signals to flash macro
  logic [PhyOps-1:0] reqs;

  // host select for address
  logic host_sel;

  // controller response valid
  logic ctrl_rsp_vld;

  // ack to phy operations from flash macro
  logic ack;

  // done to phy operations from flash macro
  logic done;

  // ack from flash_phy_prog to controller
  logic prog_ack;

  // ack from flash_phy_erase to controller
  logic erase_ack;

  // interface with flash macro
  logic [BusBankAddrW-1:0] muxed_addr;
  flash_ctrl_pkg::flash_part_e muxed_part;
  logic muxed_scramble_en;
  logic muxed_ecc_en;

  // entire read stage is idle, inclusive of all stages
  logic rd_stage_idle;

  // the read stage is ready to accept a new transaction
  logic rd_stage_rdy;

  // the read stage has valid response
  logic rd_stage_data_valid;

  // arbitration counter
  // If controller side has lost arbitration ArbCnt times, favor it once
  logic [CntWidth-1:0] arb_cnt;
  logic inc_arb_cnt;

  // scramble / de-scramble connections
  logic calc_ack;
  logic op_ack;
  logic [DataWidth-1:0] scramble_mask;

  logic host_gnt;
  logic ctrl_gnt;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      arb_cnt <= '0;
    end else if (ctrl_rsp_vld) begin
      arb_cnt <= '0;
    end else if (inc_arb_cnt) begin
      arb_cnt <= arb_cnt + 1'b1;
    end
  end

  import prim_mubi_pkg::mubi4_test_false_strict;
  import prim_mubi_pkg::mubi4_test_true_loose;

  // SEC_CM: PHY.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, StIdle)

  typedef enum logic [2:0] {
    HostDisableIdx,
    CtrlDisableIdx,
    FsmDisableIdx,
    ScrDisableIdx,
    ProgFsmDisableIdx,
    LastDisableIdx
  } phy_core_disable_e;

  prim_mubi_pkg::mubi4_t [LastDisableIdx-1:0] flash_disable;
  prim_mubi4_sync #(
    .NumCopies(int'(LastDisableIdx)),
    .AsyncOn(0)
  ) u_disable_buf (
    .clk_i,
    .rst_ni,
    .mubi_i(flash_disable_i),
    .mubi_o(flash_disable)
  );

  logic host_req;
  assign host_req = host_req_i & (arb_cnt < ArbCnt[CntWidth-1:0]) & ~ctrl_gnt &
                    mubi4_test_false_strict(flash_disable[HostDisableIdx]);
  assign host_sel = host_req;
  assign host_gnt = host_req & host_req_rdy_o;

  assign host_req_rdy_o = rd_stage_rdy & (arb_cnt < ArbCnt[CntWidth-1:0]) & ~ctrl_gnt;
  assign host_req_done_o = ~ctrl_gnt & rd_stage_data_valid;

  // oustanding width is slightly larger to ensure a faulty increment is able to reach
  // the higher value. For example if RspOrderDepth were 3, a clog2 of 3 would still be 2
  // and not allow the counter to increment to 4.
  localparam int OutstandingRdWidth = $clog2(RspOrderDepth+2);
  logic [OutstandingRdWidth-1:0] host_outstanding;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      host_outstanding <= '0;
    end else if (host_gnt && !host_req_done_o) begin
      host_outstanding <= host_outstanding + 1'b1;
    end else if (!host_gnt && host_req_done_o) begin
      host_outstanding <= host_outstanding - 1'b1;
    end
  end
  `ASSERT(RdTxnCheck_A, host_outstanding <= RspOrderDepth)


  // controller request can only win after the entire read pipeline
  // clears
  logic ctrl_req;
  assign ctrl_req = req_i & rd_stage_idle & ~host_req &
                    mubi4_test_false_strict(flash_disable[CtrlDisableIdx]);

  // if request happens at the same time as a host grant, increment count
  assign inc_arb_cnt = req_i & host_gnt;

  logic fsm_err;
  logic ctrl_fsm_idle;
  always_comb begin
    state_d = state_q;
    reqs = '0;
    ctrl_rsp_vld = '0;
    ctrl_gnt = '0;
    fsm_err = '0;
    ctrl_fsm_idle = '0;

    unique case (state_q)
      StIdle: begin
        ctrl_fsm_idle = 1'b1;
        if (mubi4_test_true_loose(flash_disable[FsmDisableIdx])) begin
          state_d = StDisable;
        end else if (ctrl_req && rd_i) begin
          reqs[PhyRead] = 1'b1;
          state_d = rd_stage_rdy ? StCtrlRead : state_q;
        end else if (ctrl_req && prog_i) begin
          state_d = StCtrlProg;
        end else if (ctrl_req) begin
          state_d = StCtrl;
        end
      end

      // Controller reads are very slow.
      StCtrlRead: begin
        ctrl_gnt = 1'b1;
        if (rd_stage_data_valid) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      // Controller program data may be packed based on
      // address alignment
      StCtrlProg: begin
        ctrl_gnt = 1'b1;
        reqs[PhyProg] = 1'b1;
        if (prog_ack) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      // other controller operations directly interface with flash
      StCtrl: begin
        ctrl_gnt = 1'b1;
        reqs[PhyPgErase] = pg_erase_i;
        reqs[PhyBkErase] = bk_erase_i;
        if (erase_ack) begin
          ctrl_rsp_vld = 1'b1;
          state_d = StIdle;
        end
      end

      StDisable: begin
        state_d = StDisable;
      end

      StInvalid: begin
        state_d = StInvalid;
        fsm_err = 1'b1;
      end

      default: begin
        state_d = StInvalid;
      end

    endcase // unique case (state_q)
  end // always_comb

  // determine spurious acks
  assign spurious_ack_o = (ctrl_fsm_idle & ctrl_rsp_vld) |
                          ((host_outstanding == '0) & host_req_done_o);

  // transactions coming from flash controller are always data type
  assign muxed_addr = host_sel ? host_addr_i : addr_i;
  assign muxed_part = host_sel ? flash_ctrl_pkg::FlashPartData : part_i;
  assign muxed_scramble_en = host_sel ? host_scramble_en_i : scramble_en_i;
  assign muxed_ecc_en = host_sel ? host_ecc_en_i : ecc_en_i;
  assign rd_done_o = ctrl_rsp_vld & rd_i;
  assign prog_done_o = ctrl_rsp_vld & prog_i;
  assign erase_done_o = ctrl_rsp_vld & (pg_erase_i | bk_erase_i);

  ////////////////////////
  // read pipeline
  ////////////////////////

  logic flash_rd_req;
  logic [FullDataWidth-1:0] flash_rdata;
  logic rd_calc_req;
  logic [BankAddrW-1:0] rd_calc_addr;
  logic rd_op_req;
  logic [DataWidth-1:0] rd_scrambled_data;
  logic [DataWidth-1:0] rd_descrambled_data;

  flash_phy_rd u_rd (
    .clk_i,
    .rst_ni,
    .buf_en_i(rd_buf_en_i),
    .req_i(reqs[PhyRead] | host_req),
    .descramble_i(muxed_scramble_en),
    .ecc_i(muxed_ecc_en),
    .prog_i(reqs[PhyProg]),
    .pg_erase_i(reqs[PhyPgErase]),
    .bk_erase_i(reqs[PhyBkErase]),
    .addr_i(muxed_addr),
    .part_i(muxed_part),
    // info select cannot be generated by the host
    .info_sel_i(info_sel_i),
    .rdy_o(rd_stage_rdy),
    .data_valid_o(rd_stage_data_valid),
    .data_err_o(rd_err_o),
    .data_o(rd_data_o),
    .idle_o(rd_stage_idle),
    .req_o(flash_rd_req),
    .ack_i(ack),
    .done_i(done),
    .data_i(flash_rdata),
    //scramble unit interface
    .calc_req_o(rd_calc_req),
    .calc_addr_o(rd_calc_addr),
    .descramble_req_o(rd_op_req),
    .scrambled_data_o(rd_scrambled_data),
    .calc_ack_i(calc_ack),
    .descramble_ack_i(op_ack),
    .mask_i(scramble_mask),
    .descrambled_data_i(rd_descrambled_data),
    .ecc_single_err_o,
    .ecc_addr_o,
    .relbl_ecc_err_o,
    .intg_ecc_err_o
    );

  ////////////////////////
  // program pipeline
  ////////////////////////

  logic [FullDataWidth-1:0] prog_full_data;
  logic [DataWidth-1:0] prog_scrambled_data;
  logic [DataWidth-1:0] prog_data;
  logic prog_last;
  logic flash_prog_req;
  logic prog_calc_req;
  logic prog_op_req;
  logic prog_fsm_err;

  if (WidthMultiple == 1) begin : gen_single_prog_data
    assign flash_prog_req = reqs[PhyProg];
    assign prog_data = prog_data_i[BusWidth-1:0];
    assign prog_fsm_err = '0;
  end else begin : gen_prog_data

    // SEC_CM: MEM.INTEGRITY
    flash_phy_prog u_prog (
      .clk_i,
      .rst_ni,
      .req_i(reqs[PhyProg]),
      .disable_i(flash_disable[ProgFsmDisableIdx]),
      .scramble_i(muxed_scramble_en),
      .ecc_i(muxed_ecc_en),
      .sel_i(addr_i[0 +: WordSelW]),
      .data_i(prog_data_i),
      .last_i(prog_last_i),
      .ack_i(ack),
      .done_i(done),
      .calc_ack_i(calc_ack),
      .scramble_ack_i(op_ack),
      .mask_i(scramble_mask),
      .scrambled_data_i(prog_scrambled_data),
      .calc_req_o(prog_calc_req),
      .scramble_req_o(prog_op_req),
      .req_o(flash_prog_req),
      .last_o(prog_last),
      .ack_o(prog_ack),
      .block_data_o(prog_data),
      .data_o(prog_full_data),
      .fsm_err_o(prog_fsm_err),
      .intg_err_o(prog_intg_err_o)
    );
  end

  ////////////////////////
  // erase pipeline
  ////////////////////////

  logic flash_pg_erase_req;
  logic flash_bk_erase_req;
  logic erase_suspend_req;
  flash_phy_erase u_erase (
    .clk_i,
    .rst_ni,
    .pg_erase_req_i(reqs[PhyPgErase]),
    .bk_erase_req_i(reqs[PhyBkErase]),
    .suspend_req_i(erase_suspend_req_i),
    .ack_o(erase_ack),
    .pg_erase_req_o(flash_pg_erase_req),
    .bk_erase_req_o(flash_bk_erase_req),
    .suspend_req_o(erase_suspend_req),
    .ack_i(ack),
    .done_i(done)
  );

  ////////////////////////
  // scrambling / de-scrambling primitive
  ////////////////////////

  logic [BankAddrW-1:0] scramble_muxed_addr;
  assign scramble_muxed_addr = prog_calc_req ? muxed_addr[BusBankAddrW-1:LsbAddrBit] :
                                               rd_calc_addr;

  // SEC_CM: MEM.SCRAMBLE
  flash_phy_scramble #(
    .SecScrambleEn(SecScrambleEn)
  ) u_scramble (
    .clk_i,
    .rst_ni,
    // both escalation and and integrity error cause the scramble keys to change
    .disable_i(mubi4_test_true_loose(flash_disable[ScrDisableIdx])),
    .calc_req_i(prog_calc_req | rd_calc_req),
    .op_req_i(prog_op_req | rd_op_req),
    .op_type_i(prog_op_req ? ScrambleOp : DeScrambleOp),
    .addr_i(scramble_muxed_addr),
    .plain_data_i(prog_data),
    .scrambled_data_i(rd_scrambled_data),
    .addr_key_i,
    .data_key_i,
    .rand_addr_key_i,
    .rand_data_key_i,
    .calc_ack_o(calc_ack),
    .op_ack_o(op_ack),
    .mask_o(scramble_mask),
    .plain_data_o(rd_descrambled_data),
    .scrambled_data_o(prog_scrambled_data)
  );

  assign fsm_err_o = fsm_err | prog_fsm_err;

  ////////////////////////
  // Actual connection to flash phy
  ////////////////////////

  // Connections to the actual flash macro wrapper
  assign prim_flash_req_o = '{
    rd_req: flash_rd_req,
    prog_req: flash_prog_req,
    prog_last: prog_last,
    prog_type: prog_type_i,
    pg_erase_req: flash_pg_erase_req,
    bk_erase_req: flash_bk_erase_req,
    erase_suspend_req: erase_suspend_req,
    // high endurance enable does not cause changes to
    // transaction protocol and is forwarded directly to the wrapper
    he: he_en_i,
    addr: muxed_addr[BusBankAddrW-1:LsbAddrBit],
    part: muxed_part,
    info_sel: info_sel_i,
    prog_full_data: prog_full_data
  };

  assign ack = prim_flash_rsp_i.ack;
  assign done = prim_flash_rsp_i.done;
  assign flash_rdata = prim_flash_rsp_i.rdata;

  /////////////////////////////////
  // Assertions
  /////////////////////////////////

  // requests to flash must always be one hot
  `ASSERT(OneHotReqs_A, $onehot0(reqs))
  `ASSERT_INIT(NoRemainder_A, AddrBitsRemain == 0)
  `ASSERT_INIT(Pow2Multiple_A, $onehot(WidthMultiple))

  // once arb count maxes, the host request should be masked
  `ASSERT(ArbCntMax_A, arb_cnt == ArbCnt |-> !inc_arb_cnt)

  // once arb count maxes, the host request needs to be masked until the arb count is cleared
  `ASSERT(CtrlPrio_A, arb_cnt == ArbCnt |-> (!host_req throughout (ctrl_rsp_vld[->1])))

endmodule // flash_phy_core
