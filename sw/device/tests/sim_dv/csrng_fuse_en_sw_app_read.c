// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/csrng_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/csrng/dif/dif_csrng.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/log.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"  // Generated.
#include "otp_ctrl_regs.h"                                // Generated

OTTF_DEFINE_TEST_CONFIG();

/**
 * CTR DRBG Known-Answer-Test (KAT) for GENERATE command.
 */
static void test_fuse_enable(const dif_csrng_t *csrng) {
  CHECK_STATUS_OK(
      csrng_testutils_fips_instantiate_kat(csrng, /*fail_expected=*/false));
  CHECK_STATUS_OK(csrng_testutils_fips_generate_kat(csrng));
}

/**
 * This test takes the following steps:
 *
 * - Issue an instantiate command to request entropy.
 * - Verify that SW can read the internal states.
 *
 * Note that this test has been simplified to just test the test_fuse_enable
 * path, since the HW has been updated to always hardwire the
 * EN_CSRNG_SW_APP_READ chicken switch to True. The chicken switch itself has
 * been removed from OTP.
 */
bool test_main(void) {
  dif_csrng_t csrng;
  CHECK_DIF_OK(dif_csrng_init(
      mmio_region_from_addr(TOP_DARJEELING_CSRNG_BASE_ADDR), &csrng));
  CHECK_DIF_OK(dif_csrng_configure(&csrng));

  test_fuse_enable(&csrng);
  return true;
}
