// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
interface jtag_if;
  logic tck   ;
  logic trst_n;
  logic tms   ;
  logic tdi   ;
  logic tdo   ;
  logic tdo_oe;

  modport tb (
    output tck, trst_n,
    output tms, tdi,
    input tdo, tdo_oe
  );

  modport dut (
    input tck, trst_n,
    input tms, tdi,
    output tdo, tdo_oe
  );
endinterface
