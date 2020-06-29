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
  output logic                       cmd_arb_sop_o,
  output logic                       cmd_arb_mop_o,
  output logic                       cmd_arb_eop_o,
  input logic                        cmd_arb_gnt_i,
  output logic [CmdFifoWidth-1:0]    cmd_arb_bus_o,
  // ack from core
  input logic                        cmd_ack_i,
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
  logic [3:0]              sfifo_cmd_depth;
  logic                    sfifo_cmd_push;
  logic [CmdFifoWidth-1:0] sfifo_cmd_wdata;
  logic                    sfifo_cmd_pop;
  logic                    sfifo_cmd_err;
  logic                    sfifo_cmd_not_full;
  logic                    sfifo_cmd_not_empty;

  // genbits fifo
  logic [127:0]            sfifo_genbits_rdata;
  logic                    sfifo_genbits_push;
  logic [127:0]            sfifo_genbits_wdata;
  logic                    sfifo_genbits_pop;
  logic                    sfifo_genbits_err;
  logic                    sfifo_genbits_not_full;
  logic                    sfifo_genbits_not_empty;
  
  logic [3:0]              cmd_len;
  logic                    cmd_arrived;
  logic                    cmd_fifo_zero;
  logic                    cmd_fifo_one;
  logic                    cmd_fifo_pop;
  
  logic                    cmd_ack_q, cmd_ack_d;
  logic [1:0]              cmd_ack_sts_q, cmd_ack_sts_d;
  
  
  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      cmd_ack_q       <= '0;
      cmd_ack_sts_q   <= '0;
    end else begin
      cmd_ack_q       <= cmd_ack_d;
      cmd_ack_sts_q   <= cmd_ack_sts_d;
    end

  assign  cmd_stage_err_o = sfifo_cmd_err || sfifo_genbits_err;

  //---------------------------------------------------------
  // capture the transfer length of data behind the command
  //---------------------------------------------------------

  prim_fifo_sync # (.Width(CmdFifoWidth),.Pass(0),.Depth(CmdFifoDepth))
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


  assign cmd_len = sfifo_cmd_rdata[11:8] + 4'h01;
  assign cmd_arrived = (sfifo_cmd_depth == {cmd_len});
  assign cmd_fifo_zero = (sfifo_cmd_depth == '0);
  assign cmd_fifo_one  = (sfifo_cmd_depth == 4'h01); 

  //---------------------------------------------------------
  // state machine to process command
  //---------------------------------------------------------

  typedef enum logic [2:0] {
                            IDLE = 3'h0, // idle
                            CMDA = 3'h1, // command arrival
                            ARBC = 3'h2, // arbiter request
                            ARBD = 3'h3, // arbiter request
                            CACK = 3'h4  // command ack
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
//    capt_cmd_shid = 1'b0;
    cmd_fifo_pop = 1'b0;
    cmd_arb_req_o = 1'b0;
    cmd_arb_sop_o = 1'b0;
    cmd_arb_mop_o = 1'b0;
    cmd_arb_eop_o = 1'b0;
    unique case (state_q)
      IDLE: begin
        if (!cmd_fifo_zero) begin
//          capt_cmd_shid = 1'b1;
          state_d = CMDA;
        end
      end
      CMDA: begin
        if (cmd_arrived) begin
          cmd_stage_rdy_o = 1'b0;
          state_d = ARBC;
        end
      end
      ARBC: begin
        cmd_stage_rdy_o = 1'b0;
        cmd_arb_req_o = 1'b1;
        if (cmd_arb_gnt_i) begin
          cmd_arb_sop_o = 1'b1;
          cmd_fifo_pop = 1'b1;
          if (cmd_fifo_one) begin
            cmd_arb_eop_o = 1'b1;
            state_d = CACK;
          end else begin
            state_d = ARBD;
          end
        end
      end
      ARBD: begin
        cmd_stage_rdy_o = 1'b0;
        cmd_fifo_pop = 1'b1;
        cmd_arb_req_o = 1'b1;
        if (cmd_fifo_one) begin
          cmd_arb_mop_o = 1'b1;
          cmd_arb_eop_o = 1'b1;
          state_d = CACK;
        end else begin
          cmd_arb_mop_o = 1'b1;
        end
      end
      CACK: begin
        cmd_stage_rdy_o = 1'b0;
        if (cmd_ack_i) begin
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

  assign cmd_ack_d = cmd_ack_i;
  assign cmd_stage_ack_o = cmd_ack_q;

  assign cmd_ack_sts_d = cmd_ack_sts_i;
  assign cmd_stage_ack_sts_o = cmd_ack_sts_q;

endmodule
