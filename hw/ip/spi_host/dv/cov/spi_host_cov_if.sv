// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implements functional coverage for spi_host

interface spi_host_cov_if
  (
   input logic clk_i
   );

  import uvm_pkg::*;
  import spi_host_pkg::*;
  import dv_utils_pkg::*;
  `include "dv_fcov_macros.svh"

  bit          en_full_cov = 1'b1;
  bit          en_intg_cov = 1'b1;

  ///////////////////////////////////
  // Control register cover points //
  ///////////////////////////////////

endinterface
