// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface i2c_if ();
  // interface pins
  logic scl_i;
  logic scl_o;
  logic scl_en_o;
  logic sda_i;
  logic sda_o;
  logic sda_en_o;

  task automatic wait_for_idle();
    fork
      // FIXME
      // Wait until bus free
    join
  endtask

endinterface : i2c_if
