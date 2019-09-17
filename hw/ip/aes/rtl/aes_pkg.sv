// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES package

package aes_pkg;

typedef enum logic {
  AES_ENC = 1'b0,
  AES_DEC = 1'b1
} mode_e;

typedef enum logic [2:0] {
  AES_128 = 3'b001,
  AES_192 = 3'b010,
  AES_256 = 3'b100
} key_len_e;

endpackage
