// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng command staging module
//

module csrng_cmd_stage #(
  parameter int unsigned CmdFifoWidth = 32,
  parameter int unsigned CmdFifoDepth = 16
) (
  input logic                        clk_i,
  input logic                        rst_ni,
  // command in
  input logic                        cs_enable_i,
  input logic                        cmd_stage_vld_i,
  input logic [CmdFifoWidth-1:0]     cmd_stage_bus_i,
  output logic                       cmd_stage_rdy_o,
  // command to arbiter
  output logic                       cmd_arb_req_o,
  input logic                        cmd_arb_gnt_i,
  output logic [CmdFifoWidth-1:0]    cmd_arb_bus_o,
  // ack from core
  input logic                        cmd_ack_i,
  input logic [3:0]                  cmd_ack_shid_i,
  input logic [1:0]                  cmd_ack_sts_i,
  // ack to app i/f
  output logic                       cmd_stage_ack_o,
  output logic [1:0]                 cmd_stage_ack_sts_o,
  // genbits from core
  input logic                        genbits_vld_i,
  output logic                       genbits_rdy_o,
  input logic [127:0]                genbits_bus_i,
  // genbits to app i/f
  output logic                       genbits_vld_o,
  input logic                        genbits_rdy_i,
  output logic [127:0]               genbits_bus_o,
  // error indication
  output logic                       cmd_stage_err_o
);

  // signals
  // command fifo
  logic [CmdFifoWidth-1:0] sfifo_cmd_rdata;
  logic [$clog2(CmdFifoDepth):0]   sfifo_cmd_depth;
  logic                            sfifo_cmd_push;
  logic [CmdFifoWidth-1:0]         sfifo_cmd_wdata;
  logic                            sfifo_cmd_pop;
  logic                            sfifo_cmd_err;
  logic                            sfifo_cmd_not_full;
  logic                            sfifo_cmd_not_empty;

  // genbits fifo
  logic [127:0]                    sfifo_genbits_rdata;
//  logic [1:0]                      sfifo_genbits_depth;
  logic                            sfifo_genbits_push;
  logic [127:0]                    sfifo_genbits_wdata;
  logic                            sfifo_genbits_pop;
  logic                            sfifo_genbits_err;
  logic                            sfifo_genbits_not_full;
  logic                            sfifo_genbits_not_empty;

  logic [3:0]                      cmd_len;
  logic                            cmd_arrived;
  logic                            cmd_fifo_zero;
  logic                            cmd_fifo_pop;
  logic                            capt_cmd_shid;
  logic                            shid_match;

  logic [3:0]                      cmd_shid_q, cmd_shid_d;


  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      cmd_shid_q   <= '0;
    end else begin
      cmd_shid_q   <= cmd_shid_d;
    end

  assign  cmd_stage_err_o = sfifo_cmd_err || sfifo_genbits_err;

  //---------------------------------------------------------
  // capture the transfer length of data behind the command
  //---------------------------------------------------------

  prim_fifo_sync # (.Width(32),.Pass(0),.Depth(CmdFifoDepth))
    u_prim_fifo_cmd
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!cs_enable_i),
       .wvalid         (sfifo_cmd_push),
       .wready         (sfifo_cmd_not_full),
       .wdata          (sfifo_cmd_wdata),
       .rvalid         (sfifo_cmd_not_empty),
       .rready         (sfifo_cmd_pop),
       .rdata          (sfifo_cmd_rdata),
       .depth          (sfifo_cmd_depth)
       );

  assign sfifo_cmd_wdata = cmd_stage_bus_i;

  assign sfifo_cmd_push = cs_enable_i && cmd_stage_vld_i;

  assign sfifo_cmd_pop = cs_enable_i && cmd_fifo_pop;

  assign cmd_arb_bus_o = sfifo_cmd_rdata;

  assign sfifo_cmd_err =
         (sfifo_cmd_push && !sfifo_cmd_not_full) ||
         (sfifo_cmd_pop && !sfifo_cmd_not_empty);


  assign cmd_len = sfifo_cmd_wdata[11:8] + 4'h01;
  assign cmd_arrived = (sfifo_cmd_depth == {1'b0,cmd_len});
  assign cmd_fifo_zero = (sfifo_cmd_depth == '0);
  assign cmd_shid_d = capt_cmd_shid ? sfifo_cmd_wdata[7:4] : cmd_shid_q;
  assign shid_match = (cmd_shid_q == cmd_ack_shid_i);

  //---------------------------------------------------------
  // state machine to process command
  //---------------------------------------------------------

  typedef enum logic [1:0] {
                            IDLE = 2'b00, // idle
                            CMDA = 2'b01, // command arrival
                            ARBR = 2'b10, // arbiter request
                            CACK = 2'b11  // command ack
                            } state_e;

  state_e state_q, state_d;


  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      state_q    <= IDLE;
    end else begin
      state_q    <= state_d;
    end


  always_comb begin
    state_d = state_q;
    cmd_stage_rdy_o = 1'b1;
    capt_cmd_shid = 1'b0;
    cmd_fifo_pop = 1'b0;
    cmd_arb_req_o = 1'b0;
    unique case (state_q)
      IDLE: begin
        if (sfifo_cmd_push) begin
          state_d = CMDA;
        end
      end
      CMDA: begin
        if (!cmd_arrived) begin
          capt_cmd_shid = 1'b1;
        end else begin
          cmd_stage_rdy_o = 1'b0;
          state_d = ARBR;
        end
      end
      ARBR: begin
        cmd_stage_rdy_o = 1'b0;
        cmd_arb_req_o = 1'b1;
        if (cmd_arb_gnt_i && !cmd_fifo_zero) begin
          cmd_fifo_pop = 1'b1;
        end else begin
          state_d = CACK;
        end
      end
      CACK: begin
        cmd_stage_rdy_o = 1'b0;
        if (cmd_ack_i && shid_match) begin
          state_d = IDLE;
        end else begin
          state_d = CACK;
        end
      end
      default: state_d = IDLE;
    endcase
  end

  //---------------------------------------------------------
  // genbits fifo
  //---------------------------------------------------------

  prim_fifo_sync # (.Width(128),.Pass(0),.Depth(2))
    u_prim_fifo_genbits
      (
       .clk_i          (clk_i),
       .rst_ni         (rst_ni),
       .clr_i          (!cs_enable_i),
       .wvalid         (sfifo_genbits_push),
       .wready         (sfifo_genbits_not_full),
       .wdata          (sfifo_genbits_wdata),
       .rvalid         (sfifo_genbits_not_empty),
       .rready         (sfifo_genbits_pop),
       .rdata          (sfifo_genbits_rdata),
       .depth          () // sfifo_genbits_depth)
       );

  assign sfifo_genbits_wdata = genbits_bus_i;

  assign sfifo_genbits_push = cs_enable_i && genbits_vld_i;
  assign genbits_rdy_o = cs_enable_i && sfifo_genbits_not_full;

  assign sfifo_genbits_pop = genbits_vld_o && genbits_rdy_i;

  assign genbits_vld_o = cs_enable_i && sfifo_genbits_not_empty;
  assign genbits_bus_o = sfifo_genbits_rdata;


  assign sfifo_genbits_err =
         (sfifo_genbits_push && !sfifo_genbits_not_full) ||
         (sfifo_genbits_pop && !sfifo_genbits_not_empty);


  //---------------------------------------------------------
  // ack logic
  //---------------------------------------------------------
  // TODO: add any special gating for genbits
  assign cmd_stage_ack_o = cmd_ack_i;
  assign cmd_stage_ack_sts_o = cmd_ack_sts_i;

endmodule
