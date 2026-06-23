// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test runs an OTBN program that performs a SHAKE-128, SHAKE-256, and
// SHA3-256 hash of a fixed message using the  OTBN-KMAC interface.

#include "hw/top/dt/kmac.h"
#include "hw/top/dt/otbn.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/kmac_testutils.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTBN_DECLARE_APP_SYMBOLS(kmac_tlt_test);
OTBN_DECLARE_SYMBOL_ADDR(kmac_tlt_test, digest_shake_128);
OTBN_DECLARE_SYMBOL_ADDR(kmac_tlt_test, digest_shake_256);
OTBN_DECLARE_SYMBOL_ADDR(kmac_tlt_test, digest_sha3_256);

static const otbn_app_t kAppKmacTest = OTBN_APP_T_INIT(kmac_tlt_test);
static const otbn_addr_t kDigestShake128 =
    OTBN_ADDR_T_INIT(kmac_tlt_test, digest_shake_128);
static const otbn_addr_t kDigestShake256 =
    OTBN_ADDR_T_INIT(kmac_tlt_test, digest_shake_256);
static const otbn_addr_t kDigestSha3256 =
    OTBN_ADDR_T_INIT(kmac_tlt_test, digest_sha3_256);

static_assert(kDtOtbnCount >= 1,
              "This test requires at least one OTBN instance");
static_assert(kDtKmacCount >= 1,
              "This test requires at least one KMAC instance");

static dt_otbn_t kTestOtbn = (dt_otbn_t)0;
static dt_kmac_t kTestKmac = (dt_kmac_t)0;

OTTF_DEFINE_TEST_CONFIG();

static void print_digest(const char *name, const uint8_t *digest, size_t len) {
  LOG_INFO("%s digest (%d bytes):", name, (int)len);
  for (size_t i = 0; i < len; i += 8) {
    LOG_INFO("  %02d: %02x%02x%02x%02x%02x%02x%02x%02x", (int)(i / 8),
             digest[i + 0], digest[i + 1], digest[i + 2], digest[i + 3],
             digest[i + 4], digest[i + 5], digest[i + 6], digest[i + 7]);
  }
}

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  // Configure KMAC to use software entropy so we don't depend on EDN being
  // available. OTBN controls the hashing session via the app interface;
  // Ibex only needs to bring KMAC to a configured idle state.
  dif_kmac_t kmac;
  CHECK_DIF_OK(dif_kmac_init_from_dt(kTestKmac, &kmac));
  CHECK_STATUS_OK(kmac_testutils_config(&kmac, /*sideload=*/false));

  // Load and run the OTBN program that drives the KMAC session.
  dif_otbn_t otbn;
  CHECK_DIF_OK(dif_otbn_init_from_dt(kTestOtbn, &otbn));
  CHECK_STATUS_OK(otbn_testutils_load_app(&otbn, kAppKmacTest));
  CHECK_STATUS_OK(otbn_testutils_execute(&otbn));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));

  // Read the digest out of OTBN DMEM.
  uint8_t digestShake128[24 * 8];
  uint8_t digestShake256[24 * 8];
  uint8_t digestSha3256[32];

  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, sizeof(digestShake128),
                                           kDigestShake128, digestShake128));
  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, sizeof(digestShake256),
                                           kDigestShake256, digestShake256));
  CHECK_STATUS_OK(otbn_testutils_read_data(&otbn, sizeof(digestSha3256),
                                           kDigestSha3256, digestSha3256));

  print_digest("SHAKE-128", digestShake128, sizeof(digestShake128));
  print_digest("SHAKE-256", digestShake256, sizeof(digestShake256));
  print_digest("SHA3-256", digestSha3256, sizeof(digestSha3256));

  return true;
}
