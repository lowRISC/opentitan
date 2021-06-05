// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package mem_bkdr_util_pkg;
  // dep packages
  import bus_params_pkg::BUS_AW;
  import dv_utils_pkg::uint32_t;
  import prim_secded_pkg::*;
  import sram_scrambler_pkg::*;
  import uvm_pkg::*;

  typedef enum {
    MemParityNone,
    MemParityOdd,
    MemParityEven
  } mem_parity_e;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // sources
  `include "mem_bkdr_util.sv"

endpackage
