// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ana_pkg
// *Module Description: Analog (nettype) Package
//############################################################################

`ifdef __ANA_PKG
`else
`define __ANA_PKG
package ana_pkg;

`ifndef VERILATOR
`ifndef SYNTHESIS
// User define datatype A (UDT)
// typedef struct {
//     real AW;
// } A;
//
// User define resulotion function Ares (UDR)
// function automatic A Ares ( input A driver[] );
//   Ares.AW = 0.0;
//   foreach ( driver[i] )
//     Ares.AW += driver[i].AW;
// endfunction
//
// Nettype awire
// nettype A awire with Ares;

nettype real awire;
`endif
`endif

endpackage  // of ana_pkg
`endif  // of __ANA_PKG
