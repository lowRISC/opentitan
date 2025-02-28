// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// interface : gpio_straps_if

import gpio_pkg::*;
// Interface definition
interface gpio_straps_if(input logic clk, input logic rst_n);

logic strap_en; // Signal to enable straps
logic strap_en_qq;
logic strap_en_q;
gpio_straps_t sampled_straps; // Sampled gpio_i snapshot data from GPIO (DUT)

modport dut_if(input strap_en, output sampled_straps);
modport tb_if(output strap_en, input sampled_straps);

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    strap_en_q <= 0;
    strap_en_qq <= 0;
  end else begin
    strap_en_q <= strap_en;
    strap_en_qq <= strap_en_q;
  end
end
endinterface
