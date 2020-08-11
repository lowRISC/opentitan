// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: entropy_src byte allignment of entropy bits state machine module
//

module entropy_src_align_sm (
    input clk_i,
    input rst_ni,

    // ins req interface
    input  logic es_enable_i,
    input  logic es_health_fail_i,
    input  logic upstr_fifo_vld_i,
    input  logic dwstr_fifo_not_full_i,
    output logic dwstr_fifo_push_o,
    output logic es_load_byte0_o,
    output logic es_load_byte1_o,
    output logic es_load_byte2_o,
    output logic es_load_byte3_o,
    input  logic other_dwstr_fifo_empty_i,
    output logic dwstr_fifo_swap_o,
    output logic dwstr_fifo_clr_o
);


  typedef enum logic [3:0] {
    IDLE = 4'h0,
    BYTE0 = 4'h1,
    BYTE1 = 4'h2,
    BYTE2 = 4'h3,
    BYTE3 = 4'h4,
    PUSH = 4'h5,
    FCHK = 4'h6,
    SWAP = 4'h7,
    BAIL = 4'h8
  } state_e;

  state_e state_q, state_d;


  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      state_q <= IDLE;
    end else begin
      state_q <= state_d;
    end


  always_comb begin
    state_d = state_q;
    dwstr_fifo_push_o = 1'b0;
    es_load_byte0_o = 1'b0;
    es_load_byte1_o = 1'b0;
    es_load_byte2_o = 1'b0;
    es_load_byte3_o = 1'b0;
    dwstr_fifo_clr_o = 1'b0;
    dwstr_fifo_swap_o = 1'b0;
    unique case (state_q)
      //    case (state_q)
      IDLE: begin
        if (es_enable_i) begin
          state_d = BYTE0;
        end
      end
      BYTE0: begin
        if (es_health_fail_i) begin
          state_d = BAIL;
        end else if (upstr_fifo_vld_i) begin
          es_load_byte0_o = 1'b1;
          state_d = BYTE1;
        end else begin
          state_d = BYTE0;
        end
      end
      BYTE1: begin
        if (es_health_fail_i) begin
          state_d = BAIL;
        end else if (upstr_fifo_vld_i) begin
          es_load_byte1_o = 1'b1;
          state_d = BYTE2;
        end else begin
          state_d = BYTE1;
        end
      end
      BYTE2: begin
        if (es_health_fail_i) begin
          state_d = BAIL;
        end else if (upstr_fifo_vld_i) begin
          es_load_byte2_o = 1'b1;
          state_d = BYTE3;
        end else begin
          state_d = BYTE2;
        end
      end
      BYTE3: begin
        if (es_health_fail_i) begin
          state_d = BAIL;
        end else if (upstr_fifo_vld_i) begin
          es_load_byte3_o = 1'b1;
          state_d = PUSH;
        end else begin
          state_d = BYTE3;
        end
      end
      PUSH: begin
        if (es_health_fail_i) begin
          state_d = BAIL;
        end else if (dwstr_fifo_not_full_i) begin
          dwstr_fifo_push_o = 1'b1;
          state_d = FCHK;
        end else begin
          state_d = PUSH;
        end
      end
      FCHK: begin
        if (!dwstr_fifo_not_full_i) begin
          state_d = SWAP;
        end else begin
          state_d = IDLE;
        end
      end
      SWAP: begin
        if (other_dwstr_fifo_empty_i) begin
          dwstr_fifo_swap_o = 1'b1;
          state_d = IDLE;
        end else begin
          state_d = SWAP;
        end
      end
      BAIL: begin
        dwstr_fifo_clr_o = 1'b1;
        state_d = IDLE;
      end
      default: state_d = IDLE;
    endcase
  end

endmodule
