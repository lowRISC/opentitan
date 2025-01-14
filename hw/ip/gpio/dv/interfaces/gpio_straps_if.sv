// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// interface : gpio_straps_if
`ifndef GPIO_STRAPS_IF_SV
`define GPIO_STRAPS_IF_SV

import gpio_pkg::*;

// Interface definition
interface gpio_straps_if();

    logic          clk;
    logic          rst_n;
    logic          strap_en;       // Signal to enable straps
    gpio_straps_t  sampled_straps; // Sampled gpio_i snapshot data from GPIO (DUT)

    modport straps_port_in(input  clk,
                           input  rst_n,
                           input  strap_en,
                           output sampled_straps);

    modport straps_port_out(output  clk,
                            output  rst_n,
                            output  strap_en,
                            input sampled_straps);

    // Sequence to capture the timing relationship between strap_en and strap_data
    sequence strap_data_timing_seq;
        @(posedge clk) strap_en ##1 sampled_straps.data;
    endsequence

    // Property for the strap_data timing
    property strap_data_timing_prop;
        strap_data_timing_seq;
    endproperty

    // Cover the property
    COV_STRAP_DATA_TIMING: cover property (strap_data_timing_prop);

    // Sequence to capture the timing relationship between rst_n and strap_en
    sequence reset_timing_seq;
        @(posedge clk) rst_n ##1 strap_en;
    endsequence

    // Property for the reset timing
    property reset_timing_prop;
        reset_timing_seq;
    endproperty

    // Cover the property
    COV_STRAP_RST_TIMING: cover property (reset_timing_prop);

    // Additional checks for early strap_en
    property strap_en_too_early_prop;
        @(posedge clk) rst_n ##[1:$] strap_en;
    endproperty

    COV_STRAP_EN_TIMING: cover property (strap_en_too_early_prop);

endinterface : gpio_straps_if

`endif // GPIO_STRAPS_IF_SV
