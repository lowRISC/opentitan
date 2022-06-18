// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aes.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aes_testutils.h"
#include "sw/device/lib/testing/clkmgr_testutils.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// The following plaintext, key and ciphertext are extracted from Appendix C of
// the Advanced Encryption Standard (AES) FIPS Publication 197 available at
// https://www.nist.gov/publications/advanced-encryption-standard-aes

#define TIMEOUT (1000 * 1000)

static const uint32_t kPlainText[] = {
    0x33221100,
    0x77665544,
    0xbbaa9988,
    0xffeeddcc,
};

static const uint8_t kKey[] = {
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a,
    0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15,
    0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f,
};

static const uint32_t kCipherTextGold[] = {
    0xcab7a28e,
    0xbf456751,
    0x9049fcea,
    0x8960494b,
};

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

static void initialize_clkmgr(void) {
  mmio_region_t addr = mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_clkmgr_init(addr, &clkmgr));

  // Get initial hint and enable for AES clock and check both are enabled.
  dif_toggle_t clock_hint_state;
  CHECK_DIF_OK(dif_clkmgr_hintable_clock_get_hint(&clkmgr, kAesClock,
                                                  &clock_hint_state));
  CHECK(clock_hint_state == kDifToggleEnabled);
  CLKMGR_TESTUTILS_CHECK_CLOCK_HINT(clkmgr, kAesClock, kDifToggleEnabled);
}

bool test_main(void) {
  dif_aes_t aes;

  initialize_clkmgr();

#if !OT_IS_ENGLISH_BREAKFAST
  // First of all, we need to get the entropy complex up and running.
  entropy_testutils_boot_mode_init();
#endif

  // Initialise AES.
  CHECK_DIF_OK(
      dif_aes_init(mmio_region_from_addr(TOP_EARLGREY_AES_BASE_ADDR), &aes));
  CHECK_DIF_OK(dif_aes_reset(&aes));

  // Mask the key. Note that this should not be done manually. Software is
  // expected to get the key in two shares right from the beginning.
  uint8_t key_share0[ARRAYSIZE(kKey)];
  for (int i = 0; i < ARRAYSIZE(kKey); ++i) {
    key_share0[i] = kKey[i] ^ kKeyShare1[i];
  }

  // "Convert" key share byte arrays to `dif_aes_key_share_t`.
  dif_aes_key_share_t key;
  memcpy(key.share0, key_share0, sizeof(kKey));
  memcpy(key.share1, kKeyShare1, sizeof(kKey));

  // Setup ECB encryption transaction.
  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey256,
      .manual_operation = kDifAesManualOperationManual,
      .masking = kDifAesMaskingInternalPrng,
      .mask_reseeding = kDifAesReseedPerBlock,
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

  // Initiate an AES operation with a known key, plain text and digest, write
  // AES clk hint to 0 and verify that the AES clk hint status within clkmgr now
  // reads 1 (AES is enabled), before the AES operation is complete.
  CHECK_DIF_OK(dif_aes_start(&aes, &transaction, &key, NULL));

  // "Convert" plain data byte arrays to `dif_aes_data_t`.
  dif_aes_data_t in_data_plain;
  memcpy(in_data_plain.data, kPlainText, sizeof(kPlainText));

  // Load the plain text to trigger the encryption operation.
  AES_TESTUTILS_WAIT_FOR_STATUS(&aes, kDifAesStatusInputReady, true, TIMEOUT);
  CHECK_DIF_OK(dif_aes_load_data(&aes, in_data_plain));

  // Write the PRNG_RESEED bit to reseed the internal state of the PRNG.
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerPrngReseed));
  CHECK_DIF_OK(dif_aes_trigger(&aes, kDifAesTriggerStart));
  CLKMGR_TESTUTILS_SET_AND_CHECK_CLOCK_HINT(
      clkmgr, kAesClock, kDifToggleDisabled, kDifToggleEnabled);

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
  dif_aes_data_t out_data_cipher;
  CHECK_DIF_OK(dif_aes_read_output(&aes, &out_data_cipher));

  // Finish the ECB encryption transaction.
  CHECK_DIF_OK(dif_aes_end(&aes));

  CHECK_ARRAYS_EQ(out_data_cipher.data, kCipherTextGold,
                  ARRAYSIZE(kCipherTextGold));

  return true;
}
