// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon package

package ascon_pkg;

parameter logic [63:0] IV_128  = 64'h80400c0600000000;
parameter logic [63:0] IV_128A = 64'h80800c0800000000;

parameter int ASCON_STATE_WIDTH = 320;


parameter int ASCON_OP_WIDTH      = 2;
parameter int ASCON_VARIANT_WIDTH = 2;

typedef enum logic [ASCON_OP_WIDTH-1:0] {
  ASCON_ENC  = 2'b01,
  ASCON_DEC  = 2'b10,
  ASCON_HASH = 2'b11
} ascon_op_e;

typedef enum logic [ASCON_VARIANT_WIDTH-1:0] {
  ASCON_128  = 2'b01,
  ASCON_128A = 2'b10
} ascon_variant_e;

endpackage
