// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sram_ctrl_bkdr_util_pkg;
  import bus_params_pkg::BUS_AW;
  import dv_utils_pkg::uint32_t, dv_utils_pkg::addr_range_t;
  import lc_ctrl_state_pkg::*;
  import mem_bkdr_util_pkg::*;
  import prim_secded_pkg::*;
  import sram_scrambler_pkg::*;
  import uvm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // sources
  `include "sram_ctrl_bkdr_util.sv"
endpackage
