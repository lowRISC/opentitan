// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
package otbn_pkg;
  // Data path width for BN (wide) instructions, in bit.
  parameter int WLEN = 256;

  // Alerts
  parameter int                   NumAlerts = 3;
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}};

  parameter int AlertImemUncorrectable = 0;
  parameter int AlertDmemUncorrectable = 1;
  parameter int AlertRegUncorrectable = 2;

  // Error codes
  typedef enum logic [31:0] {
    ErrCodeNoError = 32'h 0000_0000
  } err_code_e;

  typedef struct packed {
    logic valid;
    logic [128-1:0] key;
    logic [256-1:0] nonce;
  } otbn_ram_key_t;

endpackage
