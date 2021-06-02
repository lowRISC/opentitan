// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package mem_bkdr_pkg;
  // dep packages
  import uvm_pkg::*;
  import sram_scrambler_pkg::*;
  import bus_params_pkg::BUS_AW;
  import prim_secded_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"
  
  localparam int MAX_WIDTH = 64;

  // the interface classes
  `include "otp_mem_base_if.sv"
  `include "gen_mem_base_if.sv"

  // the base classes implementing the interface classes
  `include "otp_bkdr_base_if.sv"

endpackage
