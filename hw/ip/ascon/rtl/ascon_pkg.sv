// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon package

package ascon_pkg;

typedef enum logic [11:0] {
  // This encoding represents mubi4True and mubi4False
  MSG_IN = {4'h6, 4'h9, 4'h9},
  AD_IN =  {4'h9, 4'h6, 4'h9},
  TAG_IN = {4'h9, 4'h9, 4'h6},
  NONE =   {4'h9, 4'h9, 4'h9}
} data_type_e;


endpackage
