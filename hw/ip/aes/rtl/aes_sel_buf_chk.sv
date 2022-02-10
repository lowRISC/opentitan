// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES mux selector buffer and checker
//
// When using sparse encodings for mux selector signals, this module can be used to:
// 1. Prevent aggressive synthesis optimizations on the selector signal, and
// 2. to check that the selector signal is valid, i.e., doesn't take on invalid values.
// Whenever the selector signal takes on an invalid value, an error is signaled.

`include "prim_assert.sv"

module aes_sel_buf_chk #(
  parameter int Num      = 2,
  parameter int Width    = 1,
  parameter bit EnSecBuf = 1'b0
) (
  input  logic             clk_i,  // Used for assertions only.
  input  logic             rst_ni, // Used for assertions only.
  input  logic [Width-1:0] sel_i,
  output logic [Width-1:0] sel_o,
  output logic             err_o
);

  import aes_pkg::*;

  // Tie off unused inputs.
  logic unused_clk;
  logic unused_rst;
  assign unused_clk = clk_i;
  assign unused_rst = rst_ni;

  ////////////
  // Buffer //
  ////////////

  if (EnSecBuf) begin : gen_sec_buf
    prim_sec_anchor_buf #(
      .Width ( Width )
    ) u_prim_buf_sel_i (
      .in_i  ( sel_i ),
      .out_o ( sel_o )
    );
  end else begin : gen_buf
    prim_buf  #(
      .Width ( Width )
    ) u_prim_buf_sel_i (
      .in_i  ( sel_i ),
      .out_o ( sel_o )
    );
  end

  /////////////
  // Checker //
  /////////////

  if (Num == 2) begin : gen_mux2_sel_chk
    // Cast to generic type.
    mux2_sel_e sel_chk;
    assign sel_chk = mux2_sel_e'(sel_o);

    // Actual checker
    always_comb begin : mux2_sel_chk
      unique case (sel_chk)
        MUX2_SEL_0,
        MUX2_SEL_1: err_o = 1'b0;
        default:    err_o = 1'b1;
      endcase
    end

    // Assertion
    `ASSERT(AesMux2SelValid, !err_o |-> sel_chk inside {
        MUX2_SEL_0,
        MUX2_SEL_1
        })

  end else if (Num == 3) begin : gen_mux3_sel_chk
    // Cast to generic type.
    mux3_sel_e sel_chk;
    assign sel_chk = mux3_sel_e'(sel_o);

    // Actual checker
    always_comb begin : mux3_sel_chk
      unique case (sel_chk)
        MUX3_SEL_0,
        MUX3_SEL_1,
        MUX3_SEL_2: err_o = 1'b0;
        default:    err_o = 1'b1;
      endcase
    end

    // Assertion
    `ASSERT(AesMux3SelValid, !err_o |-> sel_chk inside {
        MUX3_SEL_0,
        MUX3_SEL_1,
        MUX3_SEL_2
        })

  end else if (Num == 4) begin : gen_mux4_sel_chk
    // Cast to generic type.
    mux4_sel_e sel_chk;
    assign sel_chk = mux4_sel_e'(sel_o);

    // Actual checker
    always_comb begin : mux4_sel_chk
      unique case (sel_chk)
        MUX4_SEL_0,
        MUX4_SEL_1,
        MUX4_SEL_2,
        MUX4_SEL_3: err_o = 1'b0;
        default:    err_o = 1'b1;
      endcase
    end

    // Assertion
    `ASSERT(AesMux4SelValid, !err_o |-> sel_chk inside {
        MUX4_SEL_0,
        MUX4_SEL_1,
        MUX4_SEL_2,
        MUX4_SEL_3
        })

  end else if (Num == 6) begin : gen_mux6_sel_chk
    // Cast to generic type.
    mux6_sel_e sel_chk;
    assign sel_chk = mux6_sel_e'(sel_o);

    // Actual checker
    always_comb begin : mux6_sel_chk
      unique case (sel_chk)
        MUX6_SEL_0,
        MUX6_SEL_1,
        MUX6_SEL_2,
        MUX6_SEL_3,
        MUX6_SEL_4,
        MUX6_SEL_5: err_o = 1'b0;
        default:    err_o = 1'b1;
      endcase
    end

    // Assertion
    `ASSERT(AesMux6SelValid, !err_o |-> sel_chk inside {
        MUX6_SEL_0,
        MUX6_SEL_1,
        MUX6_SEL_2,
        MUX6_SEL_3,
        MUX6_SEL_4,
        MUX6_SEL_5
        })

  end else begin : gen_width_unsupported
    // Selected width not supported, signal error.
    assign err_o = 1'b1;
  end

  ////////////////
  // Assertions //
  ////////////////

  // We only have generic sparse encodings defined for certain mux input numbers (see aes_pkg.sv).
  `ASSERT_INIT(AesSelBufChkNum, Num inside {2, 3, 4, 6})

endmodule
