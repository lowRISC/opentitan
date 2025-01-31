// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rom_ctrl_bkdr_util_pkg;
  import bus_params_pkg::BUS_AW;
  import dv_utils_pkg::uint32_t, dv_utils_pkg::addr_range_t;
  import lc_ctrl_state_pkg::*;
  import mem_bkdr_util_pkg::*;
  import prim_secded_pkg::*;
  // ROM scrambling uses the same properties as SRAM scrambling.
  import sram_scrambler_pkg::*;
  import uvm_pkg::*;

  parameter int ROM_DIGEST_SIZE = 256;
  parameter int ROM_DIGEST_BYTES = ROM_DIGEST_SIZE / 8;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // sources
  `include "rom_ctrl_bkdr_util.sv"
endpackage
