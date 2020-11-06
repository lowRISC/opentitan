// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng state data base module
//
// This is the container for accessing the current
//    working state for a given drbg instance.

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
  input logic                state_db_rd_req_i,
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
  output logic               state_db_sts_ack_o,
  output logic               state_db_sts_sts_o,
  output logic [StateId-1:0] state_db_sts_id_o
);

  localparam int InternalStateWidth = 2+KeyLen+BlkLen+CtrLen;

  logic [StateId-1:0]              state_db_id;
  logic [KeyLen-1:0]               state_db_key;
  logic [BlkLen-1:0]               state_db_v;
  logic [CtrLen-1:0]               state_db_rc;
  logic                            state_db_fips;
  logic                            state_db_inst_st;
  logic                            state_db_sts;
  logic                            state_db_write;
  logic                            instance_status;
  logic [InternalStateWidth-1:0] internal_states_out[NApps];

  // flops
  logic                            state_db_sts_ack_q, state_db_sts_ack_d;
  logic                            state_db_sts_sts_q, state_db_sts_sts_d;
  logic [StateId-1:0]              state_db_sts_id_q, state_db_sts_id_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      state_db_sts_ack_q   <= '0;
      state_db_sts_sts_q  <= '0;
      state_db_sts_id_q    <= '0;
    end else begin
      state_db_sts_ack_q   <= state_db_sts_ack_d;
      state_db_sts_sts_q  <= state_db_sts_sts_d;
      state_db_sts_id_q    <= state_db_sts_id_d;
    end

  // flops - no reset
  logic [InternalStateWidth-1:0]  internal_states_q[NApps], internal_states_d[NApps];


  // no reset on state
  always_ff @(posedge clk_i)
    begin
      internal_states_q  <=  internal_states_d;
    end


  //--------------------------------------------
  // read state logic
  //--------------------------------------------
  for (genvar rd = 0; rd < NApps; rd = rd+1) begin : gen_state_rd
    assign internal_states_out[rd] = (state_db_rd_req_i && (state_db_rd_inst_id_i == rd)) ?
                                     internal_states_q[rd] : '0;
  end

  if (NApps == 2) begin : gen_output_2
    assign {state_db_rd_fips_o,state_db_rd_inst_st_o,
            state_db_rd_key_o,state_db_rd_v_o,state_db_rd_res_ctr_o}
      = (state_db_rd_inst_id_i == 4'h0) ? internal_states_out[0] :
        (state_db_rd_inst_id_i == 4'h1) ? internal_states_out[1] :
        '0;
  end else if (NApps == 3) begin : g_output_3
    assign {state_db_rd_fips_o,state_db_rd_inst_st_o,
            state_db_rd_key_o,state_db_rd_v_o,state_db_rd_res_ctr_o}
      = (state_db_rd_inst_id_i == 4'h0) ? internal_states_out[0] :
        (state_db_rd_inst_id_i == 4'h1) ? internal_states_out[1] :
        (state_db_rd_inst_id_i == 4'h2) ? internal_states_out[2] :
        '0;
  end else if (NApps == 4) begin : g_output_4
    assign {state_db_rd_fips_o,state_db_rd_inst_st_o,
            state_db_rd_key_o,state_db_rd_v_o,state_db_rd_res_ctr_o}
      = (state_db_rd_inst_id_i == 4'h0) ? internal_states_out[0] :
        (state_db_rd_inst_id_i == 4'h1) ? internal_states_out[1] :
        (state_db_rd_inst_id_i == 4'h2) ? internal_states_out[2] :
        (state_db_rd_inst_id_i == 4'h3) ? internal_states_out[3] :
        '0;
  end

  // TODO: add the other NApp legs (5-15).

  //--------------------------------------------
  // write state logic
  //--------------------------------------------

  for (genvar wr = 0; wr < NApps; wr = wr+1) begin : gen_state_wr

    assign internal_states_d[wr] = (state_db_write && (state_db_id == wr)) ?
                                   {state_db_fips,state_db_inst_st,state_db_key,
                                    state_db_v,state_db_rc} : internal_states_q[wr];
  end : gen_state_wr


  assign {state_db_fips,state_db_inst_st,
          state_db_key,
          state_db_v,state_db_rc,
          state_db_id,state_db_sts} = {state_db_wr_fips_i,instance_status,
                                       state_db_wr_key_i,
                                       state_db_wr_v_i,state_db_wr_res_ctr_i,
                                       state_db_wr_inst_id_i,state_db_wr_sts_i};

  assign instance_status =
         (state_db_wr_ccmd_i == INS) ||
         (state_db_wr_ccmd_i == RES) ||
         (state_db_wr_ccmd_i == UPD);


  assign state_db_write = state_db_enable_i && state_db_wr_req_i;

  assign state_db_sts_ack_d = state_db_write;
  assign state_db_sts_sts_d = state_db_sts;
  assign state_db_sts_id_d = state_db_id;

  assign state_db_sts_ack_o = state_db_sts_ack_q;
  assign state_db_sts_sts_o = state_db_sts_sts_q;
  assign state_db_sts_id_o = state_db_sts_id_q;
  assign state_db_wr_req_rdy_o = 1'b1;

endmodule
