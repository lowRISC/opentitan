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

// NETTYPE Definition
`ifndef VERILATOR
`ifndef SYNTHESIS
  nettype real awire;
`endif
`endif
endpackage  // of ana_pkg
`endif  // of __ANA_PKG
