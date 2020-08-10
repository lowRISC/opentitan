// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_alert_handler.h"

#include "alert_handler_regs.h"  // Generated.

_Static_assert(ALERT_HANDLER_PARAM_N_CLASSES == 4,
               "Expected four alert classes!");

// This just exists to check that the header compiles for now.
