// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// No-op provider of run_vendor_tests() for the open-source rram_macro.
// A specific vendor implementation may provide a real implementation instead, adding its own
// additional tests with no open-source equivalent. See lowrisc:virtual_dv:rram_macro_vendor_tests.
//
// Every implementation of this file must drive the JTAG inputs cio_tck, cio_tdi and cio_tms, since
// tb.sv leaves them undriven. Otherwise they stay X.

`ifndef VENDOR_TESTS_SVH
`define VENDOR_TESTS_SVH

// JTAG is not used in open-source, tie the inputs off.
assign cio_tck = 1'b0;
assign cio_tdi = 1'b0;
assign cio_tms = 1'b0;

task automatic run_vendor_tests();
endtask

`endif // VENDOR_TESTS_SVH
