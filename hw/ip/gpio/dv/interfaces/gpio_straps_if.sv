// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// interface : gpio_straps_if
`ifndef GPIO_STRAPS_IF_SV
`define GPIO_STRAPS_IF_SV

import gpio_pkg::*;

// Interface definition
interface gpio_straps_if();

    logic          strap_en;       // Signal to enable straps
    gpio_straps_t  sampled_straps; // Sampled gpio_i snapshot data from GPIO (DUT)

      modport straps_port(input strap_en, output sampled_straps);

endinterface

`endif // GPIO_STRAPS_IF_SV
