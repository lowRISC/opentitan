// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// RRAM Phy Module
//
// This module wraps the open-source RRAM specific read/write data control modules that interact
// with the RRAM macro. This module also contains a shared scrambling module which is responsible
// of scrambling 128b RRAM words.

module rram_phy
  import rram_ctrl_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter rram_key_t RndCnstAddrKey = RndCnstAddrKeyDefault,
  parameter rram_key_t RndCnstDataKey = RndCnstDataKeyDefault,
  parameter bit        SecScrambleEn  = 1'b1
)
(
  input  logic                    clk_i,
  input  logic                    rst_ni,
  input  mubi4_t                  rram_disable_i,
  input  logic                    keys_valid_i,
  input  rram_key_t               addr_key_i,
  input  rram_key_t               data_key_i,
  input  rram_key_t               rand_addr_key_i,
  input  rram_key_t               rand_data_key_i,

  input  logic                    ctrl_req_i,
  input  logic                    ctrl_scramble_en_i,
  input  logic                    ctrl_ecc_en_i,
  input  logic                    ctrl_addr_xor_en_i,
  input  logic                    ctrl_rd_i,
  input  logic                    ctrl_wr_i,
  input  rram_part_e              ctrl_part_i,
  input  logic [BusAddrW-1:0]     ctrl_addr_i,
  input  logic [BusFullWidth-1:0] ctrl_wr_data_i,
  input  logic                    ctrl_wr_last_i,
  output logic                    ctrl_wr_done_o,
  output logic                    ctrl_rd_done_o,
  output logic [BusFullWidth-1:0] ctrl_rd_data_o,
  output logic                    ctrl_rd_err_o,

  input  logic                    host_req_i,
  output logic                    host_gnt_o,
  input  logic                    host_scramble_en_i,
  input  logic                    host_ecc_en_i,
  input  logic [BusAddrW-1:0]     host_addr_i,
  output logic                    host_rd_done_o,
  output logic [BusFullWidth-1:0] host_rd_data_o,
  output logic                    host_rd_err_o,
  // Status signals
  output logic                    phy_wr_busy_o,
  output logic                    phy_init_done_o,
  output logic                    ecc_corr_err_o, // correctable, connected to an interrupt
  output logic [AddrW-1:0]        ecc_corr_addr_o, // address of the last ECC error
  output rram_part_e              ecc_corr_part_o, // partition of the last ECC error
  // Error signals
  output logic                    host_gnt_err_o,
  output logic                    spurious_done_o,
  output logic                    fsm_err_o, // fatal error
  output logic                    cnt_err_o, // fatal error
  output logic                    wr_intg_err_o, // fatal error
  output logic                    rd_intg_err_o, // fatal error
  output logic                    rd_ctrl_err_o, // fatal error
  output logic                    arb_err_o, // fatal error
  output logic                    fifo_err_o, // fatal error
  output logic                    ecc_fatal_err_o, // uncorrectable
  // Interface to rram macro
  output rram_macro_req_t         rram_macro_req_o,
  input  rram_macro_rsp_t         rram_macro_rsp_i

);

  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::mubi4_test_false_strict;

  logic arb_err;
  logic host_req, host_gnt;
  logic ctrl_req, ctrl_gnt;

  logic ctrl_rd_pending;
  logic ctrl_wr_pending;

  logic phy_req;
  logic phy_rdy;
  logic phy_init_done_q;

  // phy_rd signals
  logic rd_req;
  logic rd_ack;
  logic rd_idle;

  // phy_wr signals
  logic wr_req;
  logic wr_ack;
  logic wr_done;
  logic wr_busy;

  // interface with rram macro
  logic [BusAddrW-1:0] muxed_addr;
  logic [AddrW-1:0]    rd_addr;
  logic [AddrW-1:0]    wr_addr;
  rram_part_e          rd_part;
  rram_part_e          wr_part;
  rram_part_e          muxed_part, muxed_part_buf;

  logic wr_ecc_en;
  logic rd_ecc_en;
  logic muxed_scramble_en;
  logic muxed_ecc_en;
  logic muxed_addr_xor_en;

  // scrambling module signals
  scramble_req_t [1:0] scramble_req;
  scramble_rsp_t [1:0] scramble_rsp;

  logic scramble_arb_err;
  logic wr_fsm_err;
  logic wr_cnt_err;
  logic wr_intg_err;
  logic rd_fifo_err, meta_fifo_err;

  typedef enum logic [2:0] {
    HostDisableIdx,
    CtrlDisableIdx,
    ScrambleKeyDisableIdx,
    WrFsmDisableIdx,
    LastDisableIdx
  } phy_disable_e;

  prim_mubi_pkg::mubi4_t [LastDisableIdx-1:0] rram_disable;
  prim_mubi4_sync #(
    .NumCopies(int'(LastDisableIdx)),
    .AsyncOn(0)
  ) u_disable_buf (
    .clk_i,
    .rst_ni,
    .mubi_i(rram_disable_i),
    .mubi_o(rram_disable)
  );


  // The host request is suppressed if:
  // - there is a write request pending
  // - a RRAM write operation is in progress
  // - the host is disabled
  // - phy is not initialized
  assign host_req = host_req_i & (ctrl_wr_pending == 1'b0) & (wr_busy == 1'b0) & phy_init_done_q &
                    mubi4_test_false_strict(rram_disable[HostDisableIdx]);

  // The controller request is suppressed if:
  // - there is already a controller request pending (wr or rd)
  // - a RRAM write operation is in progress
  // - phy is not initialized
  // - the controller has been disabled
  assign ctrl_req = ctrl_req_i & (ctrl_rd_pending == 1'b0) & (ctrl_wr_pending == 1'b0) &
                    (wr_busy == 1'b0) & phy_init_done_q &
                    mubi4_test_false_strict(rram_disable[CtrlDisableIdx]);

  prim_arbiter_tree_dup #(
    .N(2),
    .DW(2),
    .EnDataPort('0),
    .FixedArb(0)
  ) u_host_arb (
    .clk_i,
    .rst_ni,
    .req_chk_i('0),
    .req_i    ({ctrl_req, host_req}),
    .data_i   ('{default: '0}),
    .gnt_o    ({ctrl_gnt, host_gnt}),
    .idx_o    (),
    .valid_o  (phy_req),
    .data_o   (),
    .ready_i  (phy_rdy),
    .err_o    (arb_err)
  );

  // This fifo holds meta data of the outstanding requests
  logic meta_fifo_valid, meta_fifo_pop, meta_fifo_req, meta_fifo_rdy;
  logic host_rsp, ctrl_rsp;

  assign meta_fifo_req = rd_req & rd_ack;

  // The host + ctrl response is stored redundantly in this FIFO.
  prim_fifo_sync #(
    .Width       (2),
    .Pass        (0),
    .Depth       (NumOutstandingRdReq),
    .Secure      (1),
    .NeverClears (1'b1)
  ) u_meta_fifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(meta_fifo_req),
    .wready_o(meta_fifo_rdy),
    .wdata_i ({ctrl_gnt, host_gnt}),
    .depth_o (),
    .full_o  (),
    .rvalid_o(meta_fifo_valid),
    .rready_i(meta_fifo_pop),
    .rdata_o ({ctrl_rsp, host_rsp}),
    .err_o   (meta_fifo_err)
  );
  assign phy_rdy = meta_fifo_rdy;

  logic ctrl_multi_cycle_rd, ctrl_multi_cycle_wr;

  assign ctrl_multi_cycle_rd = rd_req & rd_ack & ~ctrl_rd_done_o & ctrl_gnt;
  assign ctrl_multi_cycle_wr = wr_req & wr_ack & ~ctrl_wr_done_o & ctrl_gnt;

  // make sure there is only one controller operation in flight
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_rd_pending <= '0;
    end else if (ctrl_multi_cycle_rd) begin
      ctrl_rd_pending <= 1'b1;
    end else if (ctrl_rd_pending & ctrl_rd_done_o) begin
      ctrl_rd_pending <= 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ctrl_wr_pending <= '0;
    end else if (ctrl_multi_cycle_wr) begin
      ctrl_wr_pending <= 1'b1;
    end else if (ctrl_wr_pending & ctrl_wr_done_o) begin
      ctrl_wr_pending <= 1'b0;
    end
  end

  logic ctrl_rd_rsp, host_rd_rsp;
  assign ctrl_rd_rsp   = meta_fifo_valid & (ctrl_rsp);
  assign host_rd_rsp   = meta_fifo_valid & (host_rsp);
  assign meta_fifo_pop = ctrl_rd_done_o | host_rd_done_o;

  assign muxed_addr        = host_gnt ? host_addr_i        : ctrl_addr_i;
  assign muxed_part        = host_gnt ? RramPartData       : ctrl_part_i;
  assign muxed_scramble_en = host_gnt ? host_scramble_en_i : ctrl_scramble_en_i;
  assign muxed_ecc_en      = host_gnt ? host_ecc_en_i      : ctrl_ecc_en_i;
  // Host TL accesses never go to OTP pages, so addr_xor is always enabled for host
  assign muxed_addr_xor_en = host_gnt ? 1'b1               : ctrl_addr_xor_en_i;

  // without this buffer host_gnt_err will get optimized away
  prim_buf #(
    .Width($bits(rram_part_e))
  ) u_prim_buf_muxed_part (
    .in_i ({muxed_part}),
    .out_o({muxed_part_buf})
  );

  assign wr_req = phy_req & ctrl_wr_i & ctrl_gnt;
  assign rd_req = phy_req & ((ctrl_rd_i & ctrl_gnt) | host_gnt);

  ///////////////////////////
  // RRAM phy read handler //
  ///////////////////////////
  logic [BusFullWidth-1:0] rd_data;
  logic                    data_err;
  logic                    data_valid;
  logic                    rram_wr_req;
  logic [PageW-1:0]        wr_page_addr;

  assign rram_wr_req  = rram_macro_req_o.wr_last & rram_macro_req_o.wr_req & rram_macro_rsp_i.ack;
  assign wr_page_addr = rram_macro_req_o.addr[AddrW-1 -: PageW];

  rram_phy_rd u_rram_phy_rd (
    .clk_i,
    .rst_ni,
    // RRAM phy interface
    .req_i          (rd_req),
    .ack_o          (rd_ack),
    .descramble_en_i(muxed_scramble_en),
    .ecc_en_i       (muxed_ecc_en),
    .addr_xor_en_i  (muxed_addr_xor_en),
    .wr_req_i       (rram_wr_req),
    .wr_page_addr_i (wr_page_addr),
    .wr_part_i      (rram_macro_req_o.part),
    .addr_i         (muxed_addr),
    .part_i         (muxed_part_buf),
    .data_valid_o   (data_valid),
    .data_err_o     (data_err),
    .data_o         (rd_data),
    // Scrambling Interface
    .scramble_req_o (scramble_req[0]),
    .scramble_rsp_i (scramble_rsp[0]),
    // RRAM Macro Interface
    .rd_req_o       (rram_macro_req_o.rd_req),
    .rd_ack_i       (rram_macro_req_o.rd_req & rram_macro_rsp_i.ack),
    .rd_done_i      (rram_macro_rsp_i.done),
    .rd_addr_o      (rd_addr),
    .rd_part_o      (rd_part),
    .rd_ecc_en_o    (rd_ecc_en),
    .rd_rdata_i     (rram_macro_rsp_i.rd_data),
    .rd_ecc_err_i   (rram_macro_rsp_i.ecc_err),
    .rd_err_i       (rram_macro_rsp_i.err),
    // Status signals
    .idle_o         (rd_idle),
    // Error Signals
    .intg_err_o     (rd_intg_err_o),
    .ctrl_err_o     (rd_ctrl_err_o),
    .ecc_fatal_err_o(ecc_fatal_err_o),
    .fifo_err_o     (rd_fifo_err)
  );

  assign ecc_corr_err_o  = 1'b0;
  assign ecc_corr_addr_o = '0;
  assign ecc_corr_part_o = RramPartData;

  assign ctrl_rd_done_o = ctrl_rd_rsp & data_valid;
  assign ctrl_rd_data_o = ctrl_rd_rsp ? rd_data : '0;
  assign ctrl_rd_err_o  = ctrl_rd_rsp ? data_err : 1'b0;

  logic [BusFullWidth-1:0] inv_data;
  tlul_data_integ_enc u_bus_intg (
    .data_i     ({BusWidth{1'b1}}),
    .data_intg_o(inv_data)
  );

  assign host_rd_done_o = host_rd_rsp & data_valid;
  assign host_rd_data_o = (host_rd_rsp & ~host_rd_err_o) ? rd_data : inv_data;
  assign host_rd_err_o  = host_rd_rsp ? data_err : 1'b0;
  assign host_gnt_o     = host_gnt & (rd_req & rd_ack);

  ////////////////////////////
  // RRAM phy write handler //
  ////////////////////////////
  rram_phy_wr u_rram_phy_wr (
    .clk_i,
    .rst_ni,
    .disable_i     (rram_disable[WrFsmDisableIdx]),
    .scramble_en_i (muxed_scramble_en),
    .ecc_en_i      (muxed_ecc_en),
    .addr_xor_en_i (ctrl_addr_xor_en_i),
    .rd_idle_i     (rd_idle),
    .req_i         (wr_req),
    .ack_o         (wr_ack),
    .addr_i        (ctrl_addr_i),
    .part_i        (ctrl_part_i),
    .data_i        (ctrl_wr_data_i),
    .last_i        (ctrl_wr_last_i),
    .done_o        (wr_done),
    .busy_o        (wr_busy),
    .scramble_req_o(scramble_req[1]),
    .scramble_rsp_i(scramble_rsp[1]),
    .wr_req_o      (rram_macro_req_o.wr_req),
    .wr_last_o     (rram_macro_req_o.wr_last),
    .data_o        (rram_macro_req_o.wr_data),
    .addr_o        (wr_addr),
    .part_o        (wr_part),
    .ecc_en_o      (wr_ecc_en),
    .ack_i         (rram_macro_req_o.wr_req & rram_macro_rsp_i.ack),
    .done_i        (rram_macro_rsp_i.done),
    .fsm_err_o     (wr_fsm_err),
    .cnt_err_o     (wr_cnt_err),
    .intg_err_o    (wr_intg_err)
  );
  assign ctrl_wr_done_o = (ctrl_wr_pending | (wr_req & wr_ack)) & wr_done;
  assign phy_wr_busy_o  = wr_busy;

  always_comb begin
    rram_macro_req_o.addr   = '0;
    rram_macro_req_o.part   = RramPartData;
    rram_macro_req_o.ecc_en = 1'b1;
    unique case(1'b1)
      rram_macro_req_o.rd_req: begin
        rram_macro_req_o.addr   = rd_addr;
        rram_macro_req_o.part   = rd_part;
        rram_macro_req_o.ecc_en = rd_ecc_en;
      end
      rram_macro_req_o.wr_req: begin
        rram_macro_req_o.addr   = wr_addr;
        rram_macro_req_o.part   = wr_part;
        rram_macro_req_o.ecc_en = wr_ecc_en;
      end
      default: ;
    endcase
  end

  // phy init done
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      phy_init_done_q <= '0;
    end else begin
      phy_init_done_q <= rram_macro_rsp_i.init_done;
    end
  end
  assign phy_init_done_o = phy_init_done_q;

  //////////////////////////////
  // Shared scrambling module //
  //////////////////////////////
  rram_scramble #(
    .RndCnstAddrKey(RndCnstAddrKey),
    .RndCnstDataKey(RndCnstDataKey),
    .SecScrambleEn(SecScrambleEn),
    .Interleave(1'b1)
  ) u_rram_scramble (
    .clk_i,
    .rst_ni,
    .keys_disable_i (rram_disable[ScrambleKeyDisableIdx]),
    .keys_valid_i   (keys_valid_i),
    .addr_key_i     (addr_key_i),
    .data_key_i     (data_key_i),
    .rand_addr_key_i(rand_addr_key_i),
    .rand_data_key_i(rand_data_key_i),
    .scramble_req_i (scramble_req),
    .scramble_rsp_o (scramble_rsp),
    .arb_err_o      (scramble_arb_err)
  );

  ///////////////////
  // Error signals //
  ///////////////////
  assign wr_intg_err_o = wr_intg_err;
  assign fsm_err_o     = wr_fsm_err;
  assign cnt_err_o     = wr_cnt_err;
  assign arb_err_o     = scramble_arb_err | arb_err;
  assign fifo_err_o    = rd_fifo_err | meta_fifo_err;

  logic spurious_rd_done;
  logic spurious_rd_host_done;

  assign spurious_rd_done      = ctrl_rd_done_o & host_rsp;
  assign spurious_rd_host_done = host_rd_done_o & ctrl_rsp;

  assign spurious_done_o = spurious_rd_done | spurious_rd_host_done;
  assign host_gnt_err_o  = host_gnt & ((muxed_part_buf != RramPartData) | ~host_req_i);

  /////////////////////////////////////////////////
  // These errors are processed in rram_ctrl.sv. //
  /////////////////////////////////////////////////
  logic unused_err;
  assign unused_err = rram_macro_rsp_i.fatal_err | rram_macro_rsp_i.recov_err;

  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  /////////////////////////////////////////////

endmodule // rram_phy
