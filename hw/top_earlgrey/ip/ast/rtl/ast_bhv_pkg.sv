// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast_bhv_pkg
// *Module Description: AST Behavioral Package
//############################################################################
`ifdef __AST_BHV_PKG_SV
`else
`define __AST_BHV_PKG_SV

package ast_bhv_pkg;

`ifndef SYNTHESIS
  /////////////////////////////////
  // Delay Parameters from Spec
  /////////////////////////////////
  // POKs
  parameter time VCC_POK_RDLY    = 3us;
  parameter time VCC_POK_FDLY    = 500ns;
  parameter time VCAON_POK_RDLY  = 3us;
  parameter time VCAON_POK_FDLY  = 500ns;
  parameter time VCMAIN_POK_RDLY = 3us;
  parameter time VCMAIN_POK_FDLY = 500ns;
  parameter time VIO_POK_RDLY   = 3us;
  parameter time VIO_POK_FDLY   = 500ns;
  // Main Regulator
  parameter time MPVCC_RDLY      = 5us;
  parameter time MPVCC_FDLY      = 100ns;
  parameter time MPPD_RDLY       = 50us;
  parameter time MPPD_FDLY       = 1us;
  // Clocks
  parameter time SYS_EN_RDLY     = 5us;
  parameter time USB_EN_RDLY     = 5us;
  // Reduced for simulation from 50ms
  parameter time USB_VAL_RDLY    = 80ns;  // 50ms
  parameter time USB_VAL_FDLY    = 80ns;
  parameter time IO_EN_RDLY      = 5us;
  parameter time AON_EN_RDLY     = 5us;
  parameter time RNG_EN_RDLY     = 5us;
`endif
  // ADC
  parameter int AdcCnvtClks      = 22;

endpackage  // of ast_bhv_pkg
`endif // of __AST_BHV_PKG_SV
