// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/base/macros.h"

// The default test hooks do nothing, but exist as the OTTF expects some hooks
// to exist. Additionally, they are weak symbols so they may be overridden by
// other custom test hooks.

OT_WEAK
bool manufacturer_pre_test_hook(void) { return true; }

OT_WEAK
bool manufacturer_post_test_hook(void) { return true; }
