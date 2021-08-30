// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_clock_gating #(
  parameter bit NoFpgaGate = 1'b0,
  parameter bit FpgaBufGlobal = 1'b1
) (
  input        clk_i,
  input        en_i,
  input        test_en_i,
  output logic clk_o
);

  if (NoFpgaGate) begin : gen_no_gate
    assign clk_o = clk_i;
  end else begin : gen_gate
    if (FpgaBufGlobal) begin : gen_bufgce
      // By default, we use BUFG(CE)s, i.e., global clock buffers (with enable input).
      // These resources are scarce (32 in monolithic 7 series devices) and under some
      // circumstances cannot be cascaded. They should especially be used for (gating)
      // clocks that span big parts of the design/multiple clock regions.
      BUFGCE #(
        .SIM_DEVICE("7SERIES")
      ) u_bufgce (
        .I (clk_i),
        .CE(en_i | test_en_i),
        .O (clk_o)
      );
    end else begin : gen_bufhce
      // The BUFH(CE) is a horizontal or local clock buffer (with enable input). Every clock
      // region has 12 of these buffers. They should be used for (gating) clocks that are
      // being used locally.
      BUFHCE u_bufhce (
        .I (clk_i),
        .CE(en_i | test_en_i),
        .O (clk_o)
      );
    end
  end



endmodule
