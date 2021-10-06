// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/clkmgr_testutils.h"

#include "sw/device/lib/dif/dif_clkmgr.h"

extern bool clkmgr_testutils_get_trans_clock_status(
    dif_clkmgr_t *clkmgr, dif_clkmgr_params_t params,
    dif_clkmgr_hintable_clock_t clock);

extern void clkmgr_testutils_check_trans_clock_gating(
    dif_clkmgr_t *clkmgr, dif_clkmgr_params_t params,
    dif_clkmgr_hintable_clock_t clock, bool exp_clock_enabled,
    uint32_t timeout_usec);
