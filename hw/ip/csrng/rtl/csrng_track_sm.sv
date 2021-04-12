// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng command tracking state machine module
//
//   provides debugging of command flow through csrng

module csrng_track_sm import csrng_pkg::*; #(
  parameter int Cmd = 3,
  parameter int StateId = 4
) (
  input logic                clk_i,
  input logic                rst_ni,

   // ins req interface
  input logic [StateId-1:0]  inst_id_i,
  input logic                acmd_hdr_capt_i,
  input logic [Cmd-1:0]      acmd_i,
  input logic [StateId-1:0]  shid_i,
  input logic                ctr_drbg_cmd_req_i,
  input logic                ctr_drbg_cmd_req_rdy_i,
  input logic [Cmd-1:0]      ctr_drbg_cmd_ccmd_i,
  input logic [StateId-1:0]  ctr_drbg_cmd_inst_id_i,
  input logic                updblk_arb_vld_i,
  input logic                updblk_arb_rdy_i,
  input logic [Cmd-1:0]      updblk_arb_ccmd_i,
  input logic [StateId-1:0]  updblk_arb_inst_id_i,
  input logic                benblk_arb_vld_i,
  input logic                benblk_arb_rdy_i,
  input logic [Cmd-1:0]      benblk_arb_ccmd_i,
  input logic [StateId-1:0]  benblk_arb_inst_id_i,
  input logic                benblk_updblk_ack_i,
  input logic                updblk_benblk_ack_rdy_i,
  input logic [Cmd-1:0]      benblk_cmd_i,
  input logic [StateId-1:0]  benblk_inst_id_i,
  input logic                updblk_cmdblk_ack_i,
  input logic                cmdblk_updblk_ack_rdy_i,
  input logic [Cmd-1:0]      updblk_cmdblk_ccmd_i,
  input logic [StateId-1:0]  updblk_cmdblk_inst_id_i,
  input logic                ctr_drbg_gen_req_i,
  input logic                ctr_drbg_gen_req_rdy_i,
  input logic [Cmd-1:0]      ctr_drbg_gen_ccmd_i,
  input logic [StateId-1:0]  ctr_drbg_gen_inst_id_i,
  input logic                benblk_genblk_ack_i,
  input logic                genblk_benblk_ack_rdy_i,
  input logic                updblk_genblk_ack_i,
  input logic                genblk_updblk_ack_rdy_i,
  input logic [Cmd-1:0]      updblk_ccmd_i,
  input logic [StateId-1:0]  updblk_inst_id_i,
  input logic                state_db_wr_req_i,
  input logic                state_db_wr_req_rdy_i,
  input logic                genbits_stage_vld_i,
  input logic                genbits_stage_rdy_i,
  input logic [Cmd-1:0]      state_db_wr_ccmd_i,
  input logic [StateId-1:0]  state_db_wr_inst_id_i,
  input logic                cmd_core_ack_i,
  input logic                cmd_stage_ack_i,
  output logic [7:0]         track_sm_o
);

  // signals
  logic  ben_ack_cntr_inc;
  logic  ben_ack_cntr_clr;

  // flops
  logic [1:0] ben_ack_cntr_q, ben_ack_cntr_d;


  localparam int StateWidth = 8;
  typedef    enum logic [StateWidth-1:0] {
    Idle           = 8'h00,
    InsCmdCap      = 8'h11,
    InsDrbgCmdIn   = 8'h12,
    InsDrbgUpdIn   = 8'h13,
    InsBlkEncIn    = 8'h14,
    InsDrbgCmdRtn  = 8'h15,
    InsStateDBIn   = 8'h16,
    InsCmdStageRtn = 8'h17,
    InsAppCmdBus   = 8'h18,

    ResCmdCap      = 8'h21,
    ResDrbgCmdIn   = 8'h22,
    ResDrbgUpdIn   = 8'h23,
    ResBlkEncIn    = 8'h24,
    ResDrbgCmdRtn  = 8'h25,
    ResStateDBIn   = 8'h26,
    ResCmdStageRtn = 8'h27,
    ResAppCmdBus   = 8'h28,

    GenCmdCap      = 8'h31,
    GenDrbgCmdIn   = 8'h32,
    GenDrbgUpd1In  = 8'h33,
    GenBlkEnc1In   = 8'h34,
    GenDrbgUpd1Rtn = 8'h35,
    GenDrbgCmd1Rtn = 8'h36,
    GenDrbgGenIn   = 8'h37,
    GenDrbgUpd2In  = 8'h38,
    GenBlkEnc2In   = 8'h39,
    GenDrbgUpd2Rtn = 8'h3a,
    GenDrbgGen1Rtn = 8'h3b,
    GenBlkEnc3In   = 8'h3c,
    GenDrbgGen2Rtn = 8'h3d,
    GenStateDBIn   = 8'h3e,
    GenAppCmdBus   = 8'h3f,

    UpdCmdCap      = 8'h41,
    UpdDrbgCmdIn   = 8'h42,
    UpdDrbgUpdIn   = 8'h43,
    UpdBlkEncIn    = 8'h44,
    UpdDrbgCmdRtn  = 8'h45,
    UpdStateDBIn   = 8'h46,
    UpdCmdStageRtn = 8'h47,
    UpdAppCmdBus   = 8'h48,

    UniCmdCap      = 8'h51,
    UniDrbgCmdIn   = 8'h52,
    UniDrbgUpdIn   = 8'h53,
    UniBlkEncIn    = 8'h54,
    UniDrbgCmdRtn  = 8'h55,
    UniStateDBIn   = 8'h56,
    UniCmdStageRtn = 8'h57,
    UniAppCmdBus   = 8'h58
  } state_e;

  state_e state_d, state_q;

  logic [StateWidth-1:0] state_raw_q;

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(Idle))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d ),
    .q_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      ben_ack_cntr_q      <= '0;
    end else begin
      ben_ack_cntr_q     <= ben_ack_cntr_d;
    end

  assign  ben_ack_cntr_d = ben_ack_cntr_inc ? (ben_ack_cntr_q+1) :
                           ben_ack_cntr_clr ? '0 :
                           ben_ack_cntr_q;

  assign state_q = state_e'(state_raw_q);
  assign track_sm_o = state_raw_q;

  always_comb begin
    state_d = state_q;
    ben_ack_cntr_inc = 1'b0;
    ben_ack_cntr_clr = 1'b0;
    unique case (state_q)
      Idle: begin
        if (acmd_hdr_capt_i && (inst_id_i == shid_i)) begin
          if (acmd_i == INS) begin
            state_d = InsCmdCap;
          end else if (acmd_i == RES) begin
            state_d = ResCmdCap;
          end else if (acmd_i == GEN) begin
            state_d = GenCmdCap;
          end else if (acmd_i == UPD) begin
            state_d = UpdCmdCap;
          end else if (acmd_i == UNI) begin
            state_d = UniCmdCap;
          end
        end
      end
      //-Start of Ins Cmd-----------------------------------------------------------------
      InsCmdCap: begin
        state_d = InsDrbgCmdIn;
      end
      InsDrbgCmdIn: begin
        if (ctr_drbg_cmd_req_i && ctr_drbg_cmd_req_rdy_i &&
            (ctr_drbg_cmd_ccmd_i == INS) && (ctr_drbg_cmd_inst_id_i == inst_id_i)) begin
          state_d = InsDrbgUpdIn;
        end
      end
      InsDrbgUpdIn: begin
        if (updblk_arb_vld_i && updblk_arb_rdy_i &&
            (updblk_arb_ccmd_i == INS) && (updblk_arb_inst_id_i == inst_id_i)) begin
          state_d = InsBlkEncIn;
        end
      end
      InsBlkEncIn: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == INS) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = InsDrbgCmdRtn;
        end
      end
      InsDrbgCmdRtn: begin
        if (updblk_cmdblk_ack_i && cmdblk_updblk_ack_rdy_i &&
            (updblk_cmdblk_ccmd_i == INS) && (updblk_cmdblk_inst_id_i == inst_id_i)) begin
          state_d = InsStateDBIn;
        end
      end
      InsStateDBIn: begin
        if (state_db_wr_req_i && state_db_wr_req_rdy_i &&
          (state_db_wr_ccmd_i == INS) && (state_db_wr_inst_id_i == inst_id_i)) begin
          state_d = InsCmdStageRtn;
        end
      end
      InsCmdStageRtn: begin
        if (cmd_core_ack_i) begin
          state_d = InsAppCmdBus;
        end
      end
      InsAppCmdBus: begin
        if (cmd_stage_ack_i) begin
          state_d = Idle;
        end
      end
      //-Start of Res Cmd-----------------------------------------------------------------
      ResCmdCap: begin
        state_d = ResDrbgCmdIn;
      end
      ResDrbgCmdIn: begin
        if (ctr_drbg_cmd_req_i && ctr_drbg_cmd_req_rdy_i &&
            (ctr_drbg_cmd_ccmd_i == RES) && (ctr_drbg_cmd_inst_id_i == inst_id_i)) begin
          state_d = ResDrbgUpdIn;
        end
      end
      ResDrbgUpdIn: begin
        if (updblk_arb_vld_i && updblk_arb_rdy_i &&
            (updblk_arb_ccmd_i == RES) && (updblk_arb_inst_id_i == inst_id_i)) begin
          state_d = ResBlkEncIn;
        end
      end
      ResBlkEncIn: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == RES) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = ResDrbgCmdRtn;
        end
      end
      ResDrbgCmdRtn: begin
        if (updblk_cmdblk_ack_i && cmdblk_updblk_ack_rdy_i &&
            (updblk_cmdblk_ccmd_i == RES) && (updblk_cmdblk_inst_id_i == inst_id_i)) begin
          state_d = ResStateDBIn;
        end
      end
      ResStateDBIn: begin
        if (state_db_wr_req_i && state_db_wr_req_rdy_i &&
          (state_db_wr_ccmd_i == RES) && (state_db_wr_inst_id_i == inst_id_i)) begin
          state_d = ResCmdStageRtn;
        end
      end
      ResCmdStageRtn: begin
        if (cmd_core_ack_i) begin
          state_d = ResAppCmdBus;
        end
      end
      ResAppCmdBus: begin
        if (cmd_stage_ack_i) begin
          state_d = Idle;
        end
      end
      //-Start of Gen Cmd-----------------------------------------------------------------
      GenCmdCap: begin
        state_d = GenDrbgCmdIn;
      end
      GenDrbgCmdIn: begin
        if (ctr_drbg_cmd_req_i && ctr_drbg_cmd_req_rdy_i &&
            (ctr_drbg_cmd_ccmd_i == GEN) && (ctr_drbg_cmd_inst_id_i == inst_id_i)) begin
          state_d = GenDrbgUpd1In;
        end
      end
      GenDrbgUpd1In: begin
        if (updblk_arb_vld_i && updblk_arb_rdy_i &&
            (updblk_arb_ccmd_i == GEN) && (updblk_arb_inst_id_i == inst_id_i)) begin
          state_d = GenBlkEnc1In;
        end
      end
      GenBlkEnc1In: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == GEN) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = GenDrbgUpd1Rtn;
        end
      end
      GenDrbgUpd1Rtn: begin // wait for 3 acks
        if (benblk_updblk_ack_i && updblk_benblk_ack_rdy_i &&
            (benblk_cmd_i == GEN) && (benblk_inst_id_i == inst_id_i)) begin
          if (ben_ack_cntr_q != 2) begin
            ben_ack_cntr_inc = 1'b1;
          end else begin
            ben_ack_cntr_clr = 1'b1;
            state_d = GenDrbgCmd1Rtn;
          end
        end
      end
      GenDrbgCmd1Rtn: begin
        if (updblk_cmdblk_ack_i && cmdblk_updblk_ack_rdy_i &&
            (updblk_cmdblk_ccmd_i == GEN) && (updblk_cmdblk_inst_id_i == inst_id_i)) begin
          state_d = GenDrbgGenIn;
        end
      end
      GenDrbgGenIn: begin
        if (ctr_drbg_gen_req_i && ctr_drbg_gen_req_rdy_i &&
            (ctr_drbg_gen_ccmd_i == GEN) && (ctr_drbg_gen_inst_id_i == inst_id_i)) begin
          state_d = GenBlkEnc2In;
        end
      end
      GenBlkEnc2In: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == GENB) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = GenDrbgGen1Rtn;
        end
      end
      GenDrbgGen1Rtn: begin
        if (benblk_genblk_ack_i && genblk_benblk_ack_rdy_i &&
            (benblk_cmd_i == GENB) && (benblk_inst_id_i == inst_id_i)) begin
          state_d = GenDrbgUpd2In;
        end
      end
      GenDrbgUpd2In: begin
        if (updblk_arb_vld_i && updblk_arb_rdy_i &&
            (updblk_arb_ccmd_i == GENU) && (updblk_arb_inst_id_i == inst_id_i)) begin
          state_d = GenBlkEnc3In;
        end
      end
      GenBlkEnc3In: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == GENU) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = GenDrbgUpd2Rtn;
        end
      end
      GenDrbgUpd2Rtn: begin // wait for 3 acks
        if (benblk_updblk_ack_i && updblk_benblk_ack_rdy_i &&
            (benblk_cmd_i == GENU) && (benblk_inst_id_i == inst_id_i)) begin
          if (ben_ack_cntr_q != 2) begin
            ben_ack_cntr_inc = 1'b1;
          end else begin
            ben_ack_cntr_clr = 1'b1;
            state_d = GenDrbgGen2Rtn;
          end
        end
      end
      GenDrbgGen2Rtn: begin
        if (updblk_genblk_ack_i && genblk_updblk_ack_rdy_i &&
            (updblk_ccmd_i == GENU) && (updblk_inst_id_i == inst_id_i)) begin
          state_d = GenStateDBIn;
        end
      end
      GenStateDBIn: begin
        if (state_db_wr_req_i && state_db_wr_req_rdy_i &&
            (state_db_wr_ccmd_i == GEN) && (state_db_wr_inst_id_i == inst_id_i)) begin
          state_d = GenAppCmdBus;
        end
      end
      GenAppCmdBus: begin
        if (genbits_stage_vld_i && genbits_stage_rdy_i) begin
          state_d = Idle;
        end
      end
      //-Start of Upd Cmd-----------------------------------------------------------------
      UpdCmdCap: begin
        state_d = UpdDrbgCmdIn;
      end
      UpdDrbgCmdIn: begin
        if (ctr_drbg_cmd_req_i && ctr_drbg_cmd_req_rdy_i &&
            (ctr_drbg_cmd_ccmd_i == UPD) && (ctr_drbg_cmd_inst_id_i == inst_id_i)) begin
          state_d = UpdDrbgUpdIn;
        end
      end
      UpdDrbgUpdIn: begin
        if (updblk_arb_vld_i && updblk_arb_rdy_i &&
            (updblk_arb_ccmd_i == UPD) && (updblk_arb_inst_id_i == inst_id_i)) begin
          state_d = UpdBlkEncIn;
        end
      end
      UpdBlkEncIn: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == UPD) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = UpdDrbgCmdRtn;
        end
      end
      UpdDrbgCmdRtn: begin
        if (updblk_cmdblk_ack_i && cmdblk_updblk_ack_rdy_i &&
            (updblk_cmdblk_ccmd_i == UPD) && (updblk_cmdblk_inst_id_i == inst_id_i)) begin
          state_d = UpdStateDBIn;
        end
      end
      UpdStateDBIn: begin
        if (state_db_wr_req_i && state_db_wr_req_rdy_i &&
          (state_db_wr_ccmd_i == UPD) && (state_db_wr_inst_id_i == inst_id_i)) begin
          state_d = UpdCmdStageRtn;
        end
      end
      UpdCmdStageRtn: begin
        if (cmd_core_ack_i) begin
          state_d = UpdAppCmdBus;
        end
      end
      UpdAppCmdBus: begin
        if (cmd_stage_ack_i) begin
          state_d = Idle;
        end
      end
      //-Start of Uni Cmd-----------------------------------------------------------------
      UniCmdCap: begin
        state_d = UniDrbgCmdIn;
      end
      UniDrbgCmdIn: begin
        if (ctr_drbg_cmd_req_i && ctr_drbg_cmd_req_rdy_i &&
            (ctr_drbg_cmd_ccmd_i == UNI) && (ctr_drbg_cmd_inst_id_i == inst_id_i)) begin
          state_d = UniDrbgUpdIn;
        end
      end
      UniDrbgUpdIn: begin
        if (updblk_arb_vld_i && updblk_arb_rdy_i &&
            (updblk_arb_ccmd_i == UNI) && (updblk_arb_inst_id_i == inst_id_i)) begin
          state_d = UniBlkEncIn;
        end
      end
      UniBlkEncIn: begin
        if (benblk_arb_vld_i && benblk_arb_rdy_i &&
            (benblk_arb_ccmd_i == UNI) && (benblk_arb_inst_id_i == inst_id_i)) begin
          state_d = UniDrbgCmdRtn;
        end
      end
      UniDrbgCmdRtn: begin
        if (updblk_cmdblk_ack_i && cmdblk_updblk_ack_rdy_i &&
            (updblk_cmdblk_ccmd_i == UNI) && (updblk_cmdblk_inst_id_i == inst_id_i)) begin
          state_d = UniStateDBIn;
        end
      end
      UniStateDBIn: begin
        if (state_db_wr_req_i && state_db_wr_req_rdy_i &&
          (state_db_wr_ccmd_i == UNI) && (state_db_wr_inst_id_i == inst_id_i)) begin
          state_d = UniCmdStageRtn;
        end
      end
      UniCmdStageRtn: begin
        if (cmd_core_ack_i) begin
          state_d = UniAppCmdBus;
        end
      end
      UniAppCmdBus: begin
        if (cmd_stage_ack_i) begin
          state_d = Idle;
        end
      end
      default: state_d = Idle;
    endcase
  end

endmodule
