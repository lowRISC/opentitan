// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

static dif_rstmgr_t rstmgr;

const test_config_t kTestConfig;

bool test_main(void) {
  dif_rstmgr_params_t params = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_RSTMGR_BASE_ADDR),
  };
  CHECK(dif_rstmgr_init(params, &rstmgr) == kDifRstmgrOk);

  dif_rstmgr_reset_info_bitfield_t info;
  CHECK(dif_rstmgr_reset_info_get(&rstmgr, &info) == kDifRstmgrOk);

  // Only POR reset cause should be set (assuming normal power-up).
  CHECK((info & kDifRstmgrResetInfoPor) == info);

  return true;
}
