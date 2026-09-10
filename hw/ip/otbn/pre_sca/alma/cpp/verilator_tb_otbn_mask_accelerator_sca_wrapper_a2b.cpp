// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A2B mode: arithmetic-to-boolean conversion.
// Inputs are arithmetically shared: share0[k] + share1[k] = secret[k] (mod
// 2^32).
#define MASK_OP 0x1Bu  // MASK_OP_ARITH2BOOL
#define ARITH_INPUT 1
#include "verilator_tb_mask_accelerator_impl.h"
