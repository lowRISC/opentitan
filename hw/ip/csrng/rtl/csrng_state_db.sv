// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng state data base module
//
// This is the container for accessing the current
//    working state for a given drbg instance.

`include "prim_assert.sv"

module csrng_state_db import csrng_pkg::*; #(
  parameter int NApps = 4,
  parameter int StateId = 4,
  parameter int BlkLen = 128,
  parameter int KeyLen = 256,
  parameter int CtrLen  = 32,
  parameter int Cmd     = 3
) (
  input logic                clk_i,
  input logic                rst_ni,

   // read interface
  input logic                state_db_enable_i,
  input logic [StateId-1:0]  state_db_rd_inst_id_i,
  output logic [KeyLen-1:0]  state_db_rd_key_o,
  output logic [BlkLen-1:0]  state_db_rd_v_o,
  output logic [CtrLen-1:0]  state_db_rd_res_ctr_o,
  output logic               state_db_rd_inst_st_o,
  output logic               state_db_rd_fips_o,
  // write interface
  input logic                state_db_wr_req_i,
  output logic               state_db_wr_req_rdy_o,
  input logic [StateId-1:0]  state_db_wr_inst_id_i,
  input logic                state_db_wr_fips_i,
  input logic [Cmd-1:0]      state_db_wr_ccmd_i,
  input logic [KeyLen-1:0]   state_db_wr_key_i,
  input logic [BlkLen-1:0]   state_db_wr_v_i,
  input logic [CtrLen-1:0]   state_db_wr_res_ctr_i,
  input logic                state_db_wr_sts_i,
  // status interface
  input logic                state_db_is_dump_en_i,
  input logic                state_db_reg_rd_sel_i,
  input logic                state_db_reg_rd_id_pulse_i,
  input logic [StateId-1:0]  state_db_reg_rd_id_i,
  output logic [31:0]        state_db_reg_rd_val_o,
  output logic               state_db_sts_ack_o,
  output logic               state_db_sts_sts_o,
  output logic [StateId-1:0] state_db_sts_id_o
);

  localparam int InternalStateWidth = 2+KeyLen+BlkLen+CtrLen;
  localparam int RegInternalStateWidth = 30+InternalStateWidth;
  localparam int RegW = 32;
  localparam int StateWidth = 1+1+KeyLen+BlkLen+CtrLen+StateId+1;

  logic [StateId-1:0]              state_db_id;
  logic [KeyLen-1:0]               state_db_key;
  logic [BlkLen-1:0]               state_db_v;
  logic [CtrLen-1:0]               state_db_rc;
  logic                            state_db_fips;
  logic                            state_db_inst_st;
  logic                            state_db_sts;
  logic                            state_db_write;
  logic                            instance_status;
  logic [NApps-1:0]                int_st_out_sel;
  logic [NApps-1:0]                int_st_dump_sel;
  logic [InternalStateWidth-1:0]   internal_states_out[NApps];
  logic [InternalStateWidth-1:0]   internal_states_dump[NApps];
  logic [RegInternalStateWidth-1:0] internal_state_diag;
  logic                             reg_rd_ptr_inc;

  // flops
  logic                            state_db_sts_ack_q, state_db_sts_ack_d;
  logic                            state_db_sts_sts_q, state_db_sts_sts_d;
  logic [StateId-1:0]              state_db_sts_id_q, state_db_sts_id_d;
  logic [StateId-1:0]              reg_rd_ptr_q, reg_rd_ptr_d;
  logic [StateId-1:0]              int_st_dump_id_q, int_st_dump_id_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      state_db_sts_ack_q   <= '0;
      state_db_sts_sts_q   <= '0;
      state_db_sts_id_q    <= '0;
      reg_rd_ptr_q         <= '0;
      int_st_dump_id_q     <= '0;
    end else begin
      state_db_sts_ack_q   <= state_db_sts_ack_d;
      state_db_sts_sts_q   <= state_db_sts_sts_d;
      state_db_sts_id_q    <= state_db_sts_id_d;
      reg_rd_ptr_q         <= reg_rd_ptr_d;
      int_st_dump_id_q     <= int_st_dump_id_d;
    end

  // flops - no reset
  logic [InternalStateWidth-1:0]  internal_states_q[NApps], internal_states_d[NApps];
  logic [InternalStateWidth-1:0]  internal_state_pl_q, internal_state_pl_d;
  logic [InternalStateWidth-1:0]  internal_state_pl_dump_q, internal_state_pl_dump_d;


  // no reset on state
  always_ff @(posedge clk_i)
    begin
      internal_states_q <= internal_states_d;
      internal_state_pl_q <= internal_state_pl_d;
      internal_state_pl_dump_q <= internal_state_pl_dump_d;
    end


  //--------------------------------------------
  // internal state read logic
  //--------------------------------------------
  for (genvar rd = 0; rd < NApps; rd = rd+1) begin : gen_state_rd
    assign int_st_out_sel[rd] = (state_db_rd_inst_id_i == rd);
    assign int_st_dump_sel[rd] = (int_st_dump_id_q == rd);
    assign internal_states_out[rd] = int_st_out_sel[rd] ? internal_states_q[rd] : '0;
    assign internal_states_dump[rd] = int_st_dump_sel[rd] ? internal_states_q[rd] : '0;
  end

  // since only one of the internal states is active at a time, a
  // logical "or" is made of all of the buses into one
  always_comb begin
    internal_state_pl_d = '0;
    internal_state_pl_dump_d = '0;
    for (int i = 0; i < NApps; i = i+1) begin
      internal_state_pl_d |= internal_states_out[i];
      internal_state_pl_dump_d |= internal_states_dump[i];
    end
  end

  assign {state_db_rd_fips_o,state_db_rd_inst_st_o,
          state_db_rd_key_o,state_db_rd_v_o,
          state_db_rd_res_ctr_o} = internal_state_pl_q;


  // using a copy of the internal state pipeline version for better timing
  assign internal_state_diag = {30'b0,internal_state_pl_dump_q};


  // Register access of internal state
  assign state_db_reg_rd_val_o =
         (reg_rd_ptr_q == 4'h0) ? internal_state_diag[RegW-1:0] :
         (reg_rd_ptr_q == 4'h1) ? internal_state_diag[2*RegW-1:RegW] :
         (reg_rd_ptr_q == 4'h2) ? internal_state_diag[3*RegW-1:2*RegW] :
         (reg_rd_ptr_q == 4'h3) ? internal_state_diag[4*RegW-1:3*RegW] :
         (reg_rd_ptr_q == 4'h4) ? internal_state_diag[5*RegW-1:4*RegW] :
         (reg_rd_ptr_q == 4'h5) ? internal_state_diag[6*RegW-1:5*RegW] :
         (reg_rd_ptr_q == 4'h6) ? internal_state_diag[7*RegW-1:6*RegW] :
         (reg_rd_ptr_q == 4'h7) ? internal_state_diag[8*RegW-1:7*RegW] :
         (reg_rd_ptr_q == 4'h8) ? internal_state_diag[9*RegW-1:8*RegW] :
         (reg_rd_ptr_q == 4'h9) ? internal_state_diag[10*RegW-1:9*RegW] :
         (reg_rd_ptr_q == 4'ha) ? internal_state_diag[11*RegW-1:10*RegW] :
         (reg_rd_ptr_q == 4'hb) ? internal_state_diag[12*RegW-1:11*RegW] :
         (reg_rd_ptr_q == 4'hc) ? internal_state_diag[13*RegW-1:12*RegW] :
         (reg_rd_ptr_q == 4'hd) ? internal_state_diag[14*RegW-1:13*RegW] :
         '0;

  // selects 32b fields from the internal state to be read out for diagnostics
  assign reg_rd_ptr_inc = state_db_reg_rd_sel_i;

  assign reg_rd_ptr_d =
         (!state_db_enable_i) ? 4'hf :
         (!state_db_is_dump_en_i) ? 4'hf :
         (reg_rd_ptr_q == 4'he) ? '0 :
         state_db_reg_rd_id_pulse_i ? '0 :
         reg_rd_ptr_inc ? (reg_rd_ptr_q+1) :
         reg_rd_ptr_q;


  assign int_st_dump_id_d =
         (!state_db_enable_i) ? '0 :
         state_db_reg_rd_id_pulse_i ? state_db_reg_rd_id_i :
         int_st_dump_id_q;

  //--------------------------------------------
  // write state logic
  //--------------------------------------------

  for (genvar wr = 0; wr < NApps; wr = wr+1) begin : gen_state_wr

    assign internal_states_d[wr] = !state_db_enable_i ? '0 : // better timing
                                   (state_db_write && (state_db_id == wr)) ?
                                   {state_db_fips,state_db_inst_st,state_db_key,
                                    state_db_v,state_db_rc} : internal_states_q[wr];
  end : gen_state_wr


  assign {state_db_fips,state_db_inst_st,
          state_db_key,
          state_db_v,state_db_rc,
          state_db_id,state_db_sts} = {StateWidth{state_db_enable_i}} &
                                      {state_db_wr_fips_i,instance_status,
                                       state_db_wr_key_i,
                                       state_db_wr_v_i,state_db_wr_res_ctr_i,
                                       state_db_wr_inst_id_i,state_db_wr_sts_i};

  assign instance_status =
         (state_db_wr_ccmd_i == INS) ||
         (state_db_wr_ccmd_i == RES) ||
         (state_db_wr_ccmd_i == GENU) ||
         (state_db_wr_ccmd_i == UPD);


  assign state_db_write = state_db_enable_i && state_db_wr_req_i;

  assign state_db_sts_ack_d =
         state_db_write;

  assign state_db_sts_sts_d =
         state_db_sts;

  assign state_db_sts_id_d =
         state_db_id;

  assign state_db_sts_ack_o = state_db_sts_ack_q;
  assign state_db_sts_sts_o = state_db_sts_sts_q;
  assign state_db_sts_id_o = state_db_sts_id_q;
  assign state_db_wr_req_rdy_o = 1'b1;


  // Assertions
  `ASSERT_KNOWN(IntStOutSelOneHot_A, $onehot(int_st_out_sel))

endmodule
