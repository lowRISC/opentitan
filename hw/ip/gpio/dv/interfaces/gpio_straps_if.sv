// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// interface : gpio_straps_if
`ifndef GPIO_STRAPS_IF_SV
`define GPIO_STRAPS_IF_SV

import gpio_pkg::*;

// Interface definition
interface gpio_straps_if(input logic clk, input logic rst_n);

  logic          strap_en;       // Signal to enable straps
  logic          strap_en_qq;
  logic          strap_en_q;
  gpio_straps_t  sampled_straps; // Sampled gpio_i snapshot data from GPIO (DUT)

  modport dut_if(input strap_en, output sampled_straps);
  modport tb_if(output strap_en, input sampled_straps);


    always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
          strap_en_q  <= 0;
          strap_en_qq <= 0;
      end else begin
          strap_en_q  <= strap_en;
          strap_en_qq <= strap_en_q;
      end
    end

    // Sequence to capture the timing relationship between strap_en and strap_data
    // This is used to cover that the straps are sampled after the strap_en signal is asserted
    // The toggle coverage will make sure about all the possible transitions of the strap_data signal
    `COVER(COV_STRAP_DATA_TIMING, strap_en ##1 sampled_straps.data)
    `COVER(COV_STRAP_VALID_TIMING, strap_en ##1 sampled_straps.valid)

    //sequence strap_data_timing_seq;
    //    @(posedge clk) strap_en ##1 sampled_straps.data;
    //endsequence

    // Property for the strap_data timing
    //property strap_data_timing_prop;
    //    strap_data_timing_seq;
    //endproperty

    // Cover the property
    //COV_STRAP_DATA_TIMING: cover property (strap_data_timing_prop);

    // Cover to capture the timing relationship between rst_n and strap_en
    // This is used to cover that the strap_en signal is not asserted before the reset is de-asserted
    `COVER(COV_STRAP_EN_RST_TIMING, !strap_en ##1 strap_en)

    //sequence reset_timing_seq;
    //    @(posedge clk) rst_n ##1 strap_en;
    //endsequence

    // Property for the reset timing
    //property reset_timing_prop;
    //    reset_timing_seq;
    //endproperty

    // Cover the property
    //COV_STRAP_RST_TIMING: cover property (reset_timing_prop);

   // Just to cover that strap_en is asserted anytime during the simulation.
   `COVER(COV_STRAP_EN_ANY, !strap_en ##[1:$] strap_en)

endinterface

`endif // GPIO_STRAPS_IF_SV
