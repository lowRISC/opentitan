// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_clock_buf #(
  // The following options allow a user to choose the type of buffer
  // associated with this cell.
  // NoFpgaBuf -> No fpga clock buffer is selected, this will be constructed
  //              out of LUTS.
  // RegionSel -> If 1 when NoFpgaBuf is 0, this informs the build tool to select
  //              a regional clock buffer.  If 0 when NoFpgaBuf is 0, this informs
  //              the build tool to select a global clock buffer, which is a more
  //              scarce resource.
  parameter bit NoFpgaBuf = 1'b0,
  parameter bit RegionSel = 1'b0
) (
  input clk_i,
  output logic clk_o
);

  if (NoFpgaBuf) begin : gen_no_fpga_buf
    assign clk_o = clk_i;
  end else begin : gen_fpga_buf
    if (RegionSel) begin : gen_bufr
      BUFR bufr_i (
        .I(clk_i),
        .O(clk_o)
      );
    end else begin : gen_bufg
      BUFG bufg_i (
        .I(clk_i),
        .O(clk_o)
      );
    end
  end


endmodule
