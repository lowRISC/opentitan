// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_mem_intf_pkg;

  import uvm_pkg::*;

  parameter int DATA_WIDTH = 32;
  parameter int ADDR_WIDTH = 32;
  parameter int INTG_WIDTH = 7;

  typedef enum { READ, WRITE } rw_e;

  `include "uvm_macros.svh"
  `include "ibex_mem_intf_seq_item.sv"

endpackage
