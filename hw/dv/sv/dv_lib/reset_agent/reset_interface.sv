// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface reset_interface ();
  // Inputs
  logic clk_i;
  // Outputs
  logic rst_o;

  // Drive default values
  task drive_idle(bit polarity_active_low);
    if (polarity_active_low) begin
      rst_o = 1'b1;
    end else begin
      rst_o = 1'b0;
    end
  endtask : drive_idle

endinterface : reset_interface
