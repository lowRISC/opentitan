// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package gpio_pkg;

  typedef struct packed {
    logic        valid;
    logic [31:0] data;
  } gpio_straps_t;

endpackage : gpio_pkg
