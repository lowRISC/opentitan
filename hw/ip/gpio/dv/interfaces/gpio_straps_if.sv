// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// interface : gpio_straps_if
`ifndef GPIO_STRAPS_IF_SV
`define GPIO_STRAPS_IF_SV

import gpio_pkg::*;

// Interface definition
interface gpio_straps_if (
    inout                strap_en_i,     // Input signal to enable straps
    input gpio_straps_t sampled_straps_o // Output signal of type gpio_straps_t
);

    logic strap_en;
    assign strap_en_i = strap_en;

endinterface

`endif // GPIO_STRAPS_IF_SV
