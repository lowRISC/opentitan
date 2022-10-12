// Copyright 2020 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51

interface JTAG_DV (
    input logic clk_i
);
    logic tdi;
    logic tdo;
    logic tms;
    logic trst_n;

    modport in (input tdi, tms, trst_n, output tdo);
    modport out (output tdi, tms, trst_n, input tdo);
endinterface
