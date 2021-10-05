// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/rstmgr_testutils.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/check.h"

bool rstmgr_testutils_is_reset_info(dif_rstmgr_t *rstmgr,
                                    dif_rstmgr_reset_info_bitfield_t info) {
  dif_rstmgr_reset_info_bitfield_t actual_info;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(rstmgr, &actual_info));
  return actual_info == info;
}
