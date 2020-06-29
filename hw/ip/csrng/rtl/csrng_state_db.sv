// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng state data base module
//
// This is the container for accessing the current
//    working state for a given drbg instance.

module csrng_state_db #(
  parameter int unsigned NApps = 4,
  parameter int unsigned StateId = 4,
  parameter int unsigned BlkLen = 128,
  parameter int unsigned KeyLen = 256,
  parameter int unsigned CtrLen  = 32
) (
  input                  clk_i,
  input                  rst_ni,

   // read interface
  input logic                state_db_enable_i,
  input logic                state_db_rd_req_i,
  input logic [StateId-1:0]  state_db_rd_inst_id_i,
  output logic [KeyLen-1:0]  state_db_rd_key_o,
  output logic [BlkLen-1:0]  state_db_rd_v_o,
  output logic [CtrLen-1:0]  state_db_rd_res_ctr_o,
  // write interface
  input logic                state_db_wr_req_i,
  output logic               state_db_wr_req_rdy_o,
  input logic [StateId-1:0]  state_db_wr_inst_id_i,
  input logic [KeyLen-1:0]   state_db_wr_key_i,
  input logic [BlkLen-1:0]   state_db_wr_v_i,
  input logic [CtrLen-1:0]   state_db_wr_res_ctr_i,
  input logic [1:0]          state_db_wr_sts_code_i,
  // status interface
  input logic                state_db_sts_rdy_i,
  output logic               state_db_sts_ack_o,
  output logic [1:0]         state_db_sts_code_o,
  output logic [StateId-1:0] state_db_sts_id_o,
  output logic               state_db_fifo_err_o
);

  localparam WrreqFifoDepth = 2;
  localparam WrreqFifoWidth = KeyLen+BlkLen+CtrLen+StateId+2;

  // signals
  // logic [$clog2(WrreqFifoDepth):0] sfifo_wrreq_depth;
  logic [WrreqFifoWidth-1:0]       sfifo_wrreq_rdata;
  logic                            sfifo_wrreq_push;
  logic [WrreqFifoWidth-1:0]       sfifo_wrreq_wdata;
  logic                            sfifo_wrreq_pop;
  logic                            sfifo_wrreq_err;
  logic                            sfifo_wrreq_not_full;
  logic                            sfifo_wrreq_not_empty;

  logic [StateId-1:0]              state_db_id;
  logic [KeyLen-1:0]               state_db_key;
  logic [BlkLen-1:0]               state_db_v;
  logic [CtrLen-1:0]               state_db_rc;
  logic [1:0]                      state_db_sts;
  logic [KeyLen+BlkLen+CtrLen-1:0] internal_states_out[NApps];

  // flops
  logic [KeyLen+BlkLen+CtrLen-1:0]  internal_states_q[NApps], internal_states_d[NApps];


  // no reset on state
  always_ff @(posedge clk_i)
    begin
      internal_states_q  <=  internal_states_d;
    end


  //--------------------------------------------
  // read state logic
  //--------------------------------------------
  genvar rd;
  generate
    for (rd = 0; rd < NApps; rd = rd+1) begin : g_state_rd
      assign internal_states_out[rd] = (state_db_rd_req_i && (state_db_rd_inst_id_i == rd)) ?
                                   internal_states_q[rd] : '0;
    end
  endgenerate

  generate
    if (NApps == 2) begin :g_output_2
      assign {state_db_rd_key_o,state_db_rd_v_o,state_db_rd_res_ctr_o}
        = (state_db_rd_inst_id_i == 4'h0) ? internal_states_out[0] :
          (state_db_rd_inst_id_i == 4'h1) ? internal_states_out[1] :
          '0;
    end else if (NApps == 3) begin : g_output_3
      assign {state_db_rd_key_o,state_db_rd_v_o,state_db_rd_res_ctr_o}
        = (state_db_rd_inst_id_i == 4'h0) ? internal_states_out[0] :
          (state_db_rd_inst_id_i == 4'h1) ? internal_states_out[1] :
          (state_db_rd_inst_id_i == 4'h2) ? internal_states_out[2] :
          '0;
    end else if (NApps == 4) begin : g_output_4
      assign {state_db_rd_key_o,state_db_rd_v_o,state_db_rd_res_ctr_o}
        = (state_db_rd_inst_id_i == 4'h0) ? internal_states_out[0] :
          (state_db_rd_inst_id_i == 4'h1) ? internal_states_out[1] :
          (state_db_rd_inst_id_i == 4'h2) ? internal_states_out[2] :
          (state_db_rd_inst_id_i == 4'h3) ? internal_states_out[3] :
          '0;
    end
  endgenerate

  //--------------------------------------------
  // write state logic
  //--------------------------------------------

  genvar wr;
  generate
    for (wr = 0; wr < NApps; wr = wr+1) begin : g_state_wr

      assign internal_states_d[wr] = (sfifo_wrreq_pop && (state_db_id == wr)) ?
                                    {state_db_key,state_db_v,state_db_rc} : internal_states_q[wr];
    end
  endgenerate

  prim_fifo_sync # (.Width(WrreqFifoWidth),.Pass(0),.Depth(WrreqFifoDepth))
    u_prim_fifo_sync_wrreq
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!state_db_enable_i),
       .wvalid         (sfifo_wrreq_push),
       .wready         (sfifo_wrreq_not_full),
       .wdata          (sfifo_wrreq_wdata),
       .rvalid         (sfifo_wrreq_not_empty),
       .rready         (sfifo_wrreq_pop),
       .rdata          (sfifo_wrreq_rdata),
       .depth          ()
       );

  assign sfifo_wrreq_wdata = {state_db_wr_key_i,state_db_wr_v_i,state_db_wr_res_ctr_i,
                              state_db_wr_inst_id_i,state_db_wr_sts_code_i};

  assign sfifo_wrreq_push = state_db_enable_i && state_db_wr_req_i;

  assign sfifo_wrreq_pop = state_db_enable_i && state_db_sts_rdy_i && sfifo_wrreq_not_empty;

  assign {state_db_key,state_db_v,state_db_rc,
          state_db_id,state_db_sts} = sfifo_wrreq_rdata;

  assign sfifo_wrreq_err =
         (sfifo_wrreq_push && !sfifo_wrreq_not_full) ||
         (sfifo_wrreq_pop && !sfifo_wrreq_not_empty);
  assign state_db_fifo_err_o = sfifo_wrreq_err;

  assign state_db_wr_req_rdy_o = sfifo_wrreq_not_full;

  assign state_db_sts_ack_o = sfifo_wrreq_pop;
  assign state_db_sts_code_o = state_db_sts;
  assign state_db_sts_id_o = state_db_id;

endmodule
