// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/coverage/printer.h"

// Weak default when no immutable section exports its coverage descriptor.
// Overridden by the strong `imm_shared_coverage_profile_desc` symbol exported
// from `imm_section` when linking mutable `ROM_EXT` variations with
// `imm_exports` under `--config=ot_coverage`.
OT_WEAK const coverage_profile_desc_t imm_shared_coverage_profile_desc = {
    .build_id = NULL,
    .cnts_start = NULL,
    .cnts_end = NULL,
    .status = NULL,
};
