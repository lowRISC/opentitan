// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

program prog_passthrough_host
  import spid_common::*;
(
  input clk,
  input rst_n,

  spi_if sif
);

  initial begin
    forever begin
      @(posedge clk);
    end
  end

  // TODO: Do Factory to load proper sequence for the test

endprogram : prog_passthrough_host
