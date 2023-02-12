// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/hmac_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define TIMEOUT (1000 * 1000)

OTTF_DEFINE_TEST_CONFIG();
static dif_clkmgr_t clkmgr;
static const dif_clkmgr_hintable_clock_t kHmacClock =
    kTopEarlgreyHintableClocksMainHmac;

static const dif_hmac_transaction_t kHmacTransactionConfig = {
    .digest_endianness = kDifHmacEndiannessLittle,
    .message_endianness = kDifHmacEndiannessLittle,
};

static bool is_hintable_clock_enabled(const dif_clkmgr_t *clkmgr,
                                      dif_clkmgr_hintable_clock_t clock) {
  dif_toggle_t clock_state;
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_get_enabled(clkmgr, clock, &clock_state));
  return clock_state == kDifToggleEnabled;
}

static void initialize_clkmgr(dif_clkmgr_hintable_clock_t clock) {
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(addr, &clkmgr));

  // Get initial hint and enable for AES clock and check both are enabled.
  dif_toggle_t clock_hint_state;
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_get_hint(&clkmgr, clock, &clock_hint_state));
  CHECK(clock_hint_state == kDifToggleEnabled);
  CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, clock, kDifToggleEnabled);
}

// This waits for the process to end with a looming hint, checks the hint status
// shows the clock is disabled, and reanable it. The check for process
// completion cannot be done using hmac registers since the clock will be
// disabled as soon as the process ends, so we just wait for the clkmgr hint
// status to indicate the clock is off, implying the process actually ended.
static void handle_end_of_process(dif_clkmgr_hintable_clock_t clock) {
  IBEX_SPIN_FOR(!is_hintable_clock_enabled(&clkmgr, clock), TIMEOUT);
  LOG_INFO("Done");

  // After the AES operation is complete verify that the AES clk hint status
  // within clkmgr now reads 0 again (AES is idle).
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(clkmgr, clock, kDifToggleDisabled,
                                            kDifToggleDisabled);

  // Write the HMAC clk hint to 1, read and check the HMAC output for
  // correctness.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(clkmgr, clock, kDifToggleEnabled,
                                            kDifToggleEnabled);
}

bool test_main(void) {
  dif_hmac_t hmac;

  initialize_clkmgr(kHmacClock);

  mmio_region_t base_addr = mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR);
  CHECK_DIF_OK(dif_hmac_init(base_addr, &hmac));

  // With the HMAC unit idle, write the HMAC clk hint to 0 within clkmgr to
  // indicate HMAC clk can be gated and verify that the HMAC clk hint status
  // within clkmgr reads 0 (HMAC is disabled).
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kHmacClock, kDifToggleDisabled, kDifToggleDisabled);

  // Write the HMAC clk hint to 1 within clkmgr to indicate HMAC clk can be
  // enabled.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kHmacClock, kDifToggleEnabled, kDifToggleEnabled);

  // Use HMAC in SHA256 mode to generate a 256bit key from `kRefHmacLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(&hmac, kHmacTransactionConfig));
  hmac_testutils_push_message(&hmac, (char *)kRefHmacLongKey,
                              sizeof(kRefHmacLongKey));
  LOG_INFO("Pushed message");
  hmac_testutils_check_message_length(&hmac, sizeof(kRefHmacLongKey) * 8);
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kHmacClock, kDifToggleDisabled, kDifToggleEnabled);
  LOG_INFO("Cleared hints");
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  LOG_INFO("Process");

  handle_end_of_process(kHmacClock);

  dif_hmac_digest_t key_digest;
  hmac_testutils_finish_polled(&hmac, &key_digest);
  CHECK_ARRAYS_EQ(key_digest.digest, kRefExpectedShaDigest.digest,
                  ARRAYSIZE(key_digest.digest));

  // Generate HMAC final digest, using the resulted SHA256 digest over the
  // `kRefHmacLongKey`.
  CHECK_DIF_OK(dif_hmac_mode_hmac_start(&hmac, (uint8_t *)&key_digest.digest[0],
                                        kHmacTransactionConfig));
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kHmacClock, kDifToggleDisabled, kDifToggleEnabled);
  LOG_INFO("Cleared hints");
  hmac_testutils_push_message(&hmac, kRefData, sizeof(kRefData));
  hmac_testutils_check_message_length(&hmac, sizeof(kRefData) * 8);
  CHECK_DIF_OK(dif_hmac_process(&hmac));
  LOG_INFO("Process");

  handle_end_of_process(kHmacClock);

  hmac_testutils_finish_and_check_polled(&hmac, &kRefExpectedHmacDigest);

  return true;
}
