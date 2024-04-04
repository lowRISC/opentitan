// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "hw/ip/aes/model/aes_modes.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define TIMEOUT (1000 * 1000)

// The mask share, used to mask kKey. Note that the masking should not be done
// manually. Software is expected to get the key in two shares right from the
// beginning.
static const uint8_t kKeyShare1[] = {
    0x0f, 0x1f, 0x2f, 0x3F, 0x4f, 0x5f, 0x6f, 0x7f, 0x8f, 0x9f, 0xaf,
    0xbf, 0xcf, 0xdf, 0xef, 0xff, 0x0a, 0x1a, 0x2a, 0x3a, 0x4a, 0x5a,
    0x6a, 0x7a, 0x8a, 0x9a, 0xaa, 0xba, 0xca, 0xda, 0xea, 0xfa,
};

OTTF_DEFINE_TEST_CONFIG();
static dif_clkmgr_t clkmgr;
static const dif_clkmgr_hintable_clock_t kAesClock =
    kTopEarlgreyHintableClocksMainAes;

static bool is_hintable_clock_enabled(const dif_clkmgr_t *clkmgr,
                                      dif_clkmgr_hintable_clock_t clock) {
  dif_toggle_t clock_state;
  CHECK_DIF_OK(
      dif_clkmgr_hintable_clock_get_enabled(clkmgr, clock, &clock_state));
  return clock_state == kDifToggleEnabled;
}

static status_t initialize_clkmgr(void) {
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(addr, &clkmgr));

  // Get initial hint and enable for AES clock and check both are enabled.
  dif_toggle_t clock_hint_state;
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_hint(&clkmgr, kAesClock,
                                                  &clock_hint_state));
  CHECK(clock_hint_state == kDifToggleEnabled);
  return CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, kAesClock,
                                           kDifToggleEnabled);
}

status_t execute_test(dif_aes_t *aes) {
  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[sizeof(kAesModesKey256)];
  for (int i = 0; i < sizeof(kAesModesKey256); ++i) {
    key_share0[i] = kAesModesKey256[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(key.share0));
  memcpy(key.share1, kKeyShare1, sizeof(key.share1));

  // Setup ECB decryption transaction. ECB decryption is selected because
  // operating the AES cipher in inverse operation mode requires to first
  // generate the decryption start key. As a result, the AES cipher is busy
  // for the duration of two encryption/decryption runs which gives this
  // test sufficient time to update the clock hint and verify that the clock
  // is still active.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationDecrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .manual_operation = kDifAesManualOperationAuto,
      .reseed_on_key_change = false,
      .ctrl_aux_lock = false,
  };

  // With the AES unit idle, write the AES clk hint to 0 within clkmgr to
  // indicate AES clk can be gated and verify that the AES clk hint status
  // within clkmgr reads 0 (AES is disabled).
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kAesClock, kDifToggleDisabled, kDifToggleDisabled);

  // Write the AES clk hint to 1 within clkmgr to indicate AES clk can be
  // enabled.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kAesClock, kDifToggleEnabled, kDifToggleEnabled);

  // Initiate an AES operation with a known key, cipher text and plain text,
  // write AES clk hint to 0 and verify that the AES clk hint status within
  // clkmgr now reads 1 (AES is enabled), before the AES operation is complete.
  TRY(dif_aes_start(aes, &transaction, &key, NULL));

  // "Convert" plain data byte arrays to `dif_aes_data_t`.
  dif_aes_data_t in_data_cipher;
  memcpy(in_data_cipher.data, kAesModesCipherTextEcb256,
         sizeof(in_data_cipher.data));

  // Load the plain text to trigger the encryption operation.
  AES_TESTUTILS_WAIT_FOR_STATUS(aes, kDifAesStatusInputReady, true, TIMEOUT);
  dif_result_t ret = dif_aes_load_data(aes, in_data_cipher);
  // Write the clock hint to 0 and verify that the clock is still enabled.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kAesClock, kDifToggleDisabled, kDifToggleEnabled);
  TRY(ret);

  // This is a bit awkward, but when the AES finishes the operation the clock
  // will be gated as the clock hint has requested and the AES registers can't
  // be read. So the safest way to check whether the AES has finished is by
  // checking that the clock is not gated.
  IBEX_SPIN_FOR(!is_hintable_clock_enabled(&clkmgr, kAesClock), TIMEOUT);

  // After the AES operation is complete verify that the AES clk hint status
  // within clkmgr now reads 0 again (AES is idle).
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kAesClock, kDifToggleDisabled, kDifToggleDisabled);

  // Write the AES clk hint to 1, read and check the AES output for
  // correctness.
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kAesClock, kDifToggleEnabled, kDifToggleEnabled);
  dif_aes_data_t out_data;
  TRY(dif_aes_read_output(aes, &out_data));

  // Finish the ECB decryption transaction.
  TRY(dif_aes_end(aes));
  TRY_CHECK_ARRAYS_EQ((uint8_t *)out_data.data, kAesModesPlainText,
                      sizeof(out_data.data));
  return OK_STATUS();
}

bool test_main(void) {
  dif_aes_t aes;
  CHECK_STATUS_OK(initialize_clkmgr());

  // Initialise AES.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  return status_ok(execute_test(&aes));
}
