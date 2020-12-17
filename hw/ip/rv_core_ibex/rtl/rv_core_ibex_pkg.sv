// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package rv_core_ibex_pkg;

  typedef struct packed {
    logic [top_pkg::TL_AW-1:0] last_pc_fetched;
    logic [top_pkg::TL_AW-1:0] last_pc_retired;
    logic [top_pkg::TL_AW-1:0] last_instr_addr;
    logic [top_pkg::TL_AW-1:0] last_data_addr;
  } crashdump_t;

endpackage : rv_core_ibex_pkg
