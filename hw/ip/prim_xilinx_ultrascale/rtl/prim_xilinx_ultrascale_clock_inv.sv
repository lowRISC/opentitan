// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_ultrascale_clock_inv #(
  parameter bit HasScanMode = 1'b1,
  parameter bit NoFpgaBufG = 1'b0
) (
  input clk_i,
  input scanmode_i,
  output logic clk_no    // Inverted
);

  if (NoFpgaBufG) begin : gen_no_fpga_buf
    if (HasScanMode) begin : gen_scan
      assign clk_no = scanmode_i ? clk_i : ~clk_i;
    end else begin : gen_no_scan
      assign clk_no = clk_i;
    end
  end else begin : gen_fpga_buf
    if (HasScanMode) begin : gen_scan
      BUFGCTRL #(
        .IS_I0_INVERTED(1'b1),
        .IS_S0_INVERTED(1'b1)
      ) bufg_i (
        .I0(clk_i),
        .I1(clk_i),
        .CE0(1'b1),
        .CE1(1'b1),
        .IGNORE0(1'b0),
        .IGNORE1(1'b0),
        .S0(scanmode_i),
        .S1(scanmode_i),
        .O(clk_no)
      );
    end else begin : gen_no_scan
      logic unused_scanmode;
      assign unused_scanmode = scanmode_i;

      BUFGCE #(
        .IS_I_INVERTED(1'b1)
      ) bufg_i (
        .I(clk_i),
        .CE(1'b1),
        .O(clk_no)
      );
    end
  end


endmodule
