// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module generates the galois multiply matrix for flash xex
// The matrix generation is done once at flash reset and held in flops
// This reduces the later performance penalty of calculating this value live
// Note, the storage overhead is VERY high

`include "prim_assert.sv"

module flash_gen_matrix #(
  parameter int Width = 64,
  parameter logic [Width-1:0] IPoly = 'h0
) (
  input clk_i,
  input rst_ni,
  input start_i,
  input [Width-1:0] entropy_i,
  input [Width-1:0] seed_i,
  output logic done_o,
  output logic [Width-1:0][Width-1:0] matrix_o
);

  localparam CntWidth = $clog2(Width);

  logic cnt_clr;
  logic cnt_en;
  logic matrix_random_en;
  logic matrix_update;
  logic [CntWidth-1:0] cnt;
  logic [CntWidth-1:0] cnt_prev;
  logic [Width-1:0] next_matrix_entry;
  logic [Width-1:0] prev_matrix_entry;

  typedef enum logic [1:0] {
    StReset = 'h0,
    StInit  = 'h1,
    StCalc  = 'h2,
    StDone  = 'h3
  } state_e;

  state_e st, st_nxt;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st <= StReset;
    end else begin
      st <= st_nxt;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cnt <= 'h0;
    end else if (cnt_clr) begin
      cnt <= 'h0;
    end else if (cnt_en) begin
      cnt <= cnt + 1'b1;
    end
  end

  assign cnt_prev = cnt == 0 ? '0 : cnt - 1'b1;
  assign prev_matrix_entry = matrix_o[cnt_prev];
  assign next_matrix_entry = {prev_matrix_entry[0 +: Width-1], 1'b0} ^
                             (IPoly & {Width{prev_matrix_entry[Width-1]}});

  always_ff @(posedge clk_i) begin
    if (matrix_random_en) begin
      matrix_o[cnt] <= entropy_i;
    end else if (matrix_update) begin
      if (cnt == 0) begin
        matrix_o[cnt] <= seed_i;
      end else begin
        matrix_o[cnt] <= next_matrix_entry;
      end
    end
  end

  // The following FSM manages the matrix state clearing and the eventual population of real content
  always_comb begin
    st_nxt = st;
    matrix_random_en = 1'b0;
    matrix_update = 1'b0;
    cnt_en = 1'b0;
    cnt_clr = 1'b0;
    done_o = 1'b0;

    unique case (st)
      // Need to wait for start to ensure seeds / entropy are ready
      StReset: begin
        st_nxt = start_i ? StInit : StReset;
      end

      // Populate the matrix with random values
      StInit: begin
        matrix_random_en = 1'b1;
        if (cnt < Width-1) begin
          cnt_en = 1'b1;
        end else begin
          cnt_clr = 1'b1;
          st_nxt = StCalc;
        end
      end

      // Calculate the actual matrix contents
      StCalc: begin
        matrix_update = 1'b1;
        if (cnt < Width-1) begin
          cnt_en = 1'b1;
        end else begin
          cnt_clr = 1'b1;
          st_nxt = StDone;
        end
      end

      StDone: begin
        done_o = 1'b1;
      end

      default:;
    endcase // unique case (st)
  end


  //////////////////////////////////////////////
  // Assertions, Assumptions, and Coverpoints //
  //////////////////////////////////////////////

  `ASSERT(cntEnClrExclusive_A, $onehot0( {cnt_en, cnt_clr}))
  `ASSERT(randomUpdateExclusive_A, $onehot0(
    {matrix_random_en, matrix_update}))

endmodule // flash_erase_ctrl
