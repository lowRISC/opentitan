// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * OTBN Special Purpose Registers: 32b CSRs, and WLEN WSRs
 */
module otbn_status_registers
import otbn_pkg::*;
(
    input logic clk_i,
    input logic rst_ni,

    input [WLEN-1:0] rnd_i
);

endmodule
