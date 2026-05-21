// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/impl/kats.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

#ifdef KAT_CHECK_ENABLE
// The actual state tracked by the kat evaluation
uint32_t otcrypto_fips_kat_state = 0;

// The symbol that the cryptolib expects to find during the standard link.
void *_libotcrypto_tether_ = &otcrypto_fips_kat_state;
#endif

/**
 * @brief Tests that the lazy KAT evaluation runs once and skips thereafter.
 */
status_t test_lazy_kat_execution(void) {
#ifdef KAT_CHECK_ENABLE
  LOG_INFO("Testing lazy KAT execution for FIPS build using AES...");

  TRY_CHECK(otcrypto_fips_kat_state == 0, "KAT state should be 0 initially.");

  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesEcb,
      .key_length = 16,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t keyblob[8] = {0};
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  key.checksum = otcrypto_integrity_blinded_checksum(&key);

  uint32_t iv_data[128 / 8 / sizeof(uint32_t)] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, 4);

  uint8_t input_data[16] = {0};
  otcrypto_const_byte_buf_t input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, input_data, 16);

  uint8_t output_data[16] = {0};
  otcrypto_byte_buf_t output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 16);

  // First run (should run KAT, then fail mode check)
  uint64_t t1_start = ibex_mcycle_read();
  otcrypto_status_t status1 =
      otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &input, kOtcryptoAesPaddingNull, &output);
  uint64_t t1_end = ibex_mcycle_read();
  uint64_t first_run_cycles = t1_end - t1_start;

  // Ensure it failed properly inside otcrypto_aes
  TRY_CHECK(status1.value == OTCRYPTO_BAD_ARGS.value,
            "Expected BAD_ARGS due to mode mismatch.");

  // Verify the KAT bit for AES ECB 256 was successfully set.
  TRY_CHECK((otcrypto_fips_kat_state & OTCRYPTO_KAT_AES_ECB_256_DECRYPT) != 0,
            "AES KAT bit was not set by the cryptolib.");

  // Verify NO OTHER bits were set.
  TRY_CHECK(otcrypto_fips_kat_state == OTCRYPTO_KAT_AES_ECB_256_DECRYPT,
            "Other KAT bits were erroneously set.");

  // Second run (should skip KAT, then fail mode check)
  uint64_t t2_start = ibex_mcycle_read();
  otcrypto_status_t status2 =
      otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &input, kOtcryptoAesPaddingNull, &output);
  uint64_t t2_end = ibex_mcycle_read();
  uint64_t second_run_cycles = t2_end - t2_start;

  TRY_CHECK(status2.value == OTCRYPTO_BAD_ARGS.value,
            "Expected BAD_ARGS due to mode mismatch.");

  LOG_INFO("First run (with KAT): %u cycles", (uint32_t)first_run_cycles);
  LOG_INFO("Second run (skipped KAT): %u cycles", (uint32_t)second_run_cycles);

  // Prove the second run was significantly faster
  TRY_CHECK(second_run_cycles < (first_run_cycles / 2),
            "Second run was not faster; KAT was not skipped.");

  LOG_INFO("KAT FIPS behavior verified using AES.");
#endif

  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  // Run the lazy execution proof
  CHECK_STATUS_OK(test_lazy_kat_execution());

  return true;
}
