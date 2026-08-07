// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "third_party/embedpqc/ports/mldsa_caller_common.h"

// Assumes RISC-V ABI calling conventions for passing integers and pointer arguments in a0-a7

MLDSA_CALLER_WITH_STACK(mldsa87_tiny_pub_from_seed, a2)
MLDSA_CALLER_WITH_STACK(mldsa87_tiny_sign, a5)
MLDSA_CALLER_WITH_STACK(mldsa87_tiny_sign_mu, a4)
MLDSA_CALLER_WITH_STACK(mldsa87_tiny_sign_deterministic, a4)
MLDSA_CALLER_WITH_STACK(mldsa87_tiny_sign_mu_deterministic, a3)
MLDSA_CALLER_WITH_STACK(mldsa87_tiny_verify, a4)
MLDSA_CALLER_WITH_STACK(mldsa87_tiny_verify_mu, a3)
