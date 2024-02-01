// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

// The SV side will flip POR_N and cause some AON power glitches prior to the
// start of test_main. Both of these cause a new POR, so all this has to do is
// check that the `reset_info` CSR is POR.
bool test_main(void) {
  dif_rstmgr_t rstmgr;
  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  LOG_INFO("Checking reset status.");
  CHECK(
      UNWRAP(rstmgr_testutils_reset_info_any(&rstmgr, kDifRstmgrResetInfoPor)));
  LOG_INFO("Reset status indicates a POR");

  return true;
}
