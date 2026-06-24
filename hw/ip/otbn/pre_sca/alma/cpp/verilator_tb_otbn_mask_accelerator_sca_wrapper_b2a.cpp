// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// B2A mode: boolean-to-arithmetic conversion.
// Inputs are boolean-shared: share0[k] XOR share1[k] = secret[k].
#define MASK_OP 0x0Cu  // MASK_OP_BOOL2ARITH
#define ARITH_INPUT 0
#include "verilator_tb_mask_accelerator_impl.h"
