// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_CLKMGR_OFF_TRANS_IMPL_H_
#define OPENTITAN_SW_DEVICE_TESTS_CLKMGR_OFF_TRANS_IMPL_H_

#include <stdbool.h>

#include "sw/device/lib/dif/dif_clkmgr.h"

bool execute_off_trans_test(dif_clkmgr_hintable_clock_t clock);

#endif  // OPENTITAN_SW_DEVICE_TESTS_CLKMGR_OFF_TRANS_IMPL_H_
