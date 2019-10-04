// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package bus_pkg;

  typedef struct packed {
    logic [11:0] addr;
    logic [31:0] wdata;
    logic        write;
  } bus_reg_t;

  typedef struct packed {
    logic [31:0] rdata;
  } reg_bus_t;

endpackage
