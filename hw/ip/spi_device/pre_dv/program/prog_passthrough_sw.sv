// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

program prog_passthrough_sw
  import spid_common::*;
(
  input clk,
  input rst_n
);

  initial begin
    forever begin
      @(posedge clk);
    end
  end


endprogram : prog_passthrough_sw
