// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <string.h>

#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

OTTF_DEFINE_TEST_CONFIG();

// Define the state as static (this is user's side)
static otcrypto_state_t test_cryptolib_state = {0};

/**
 * @brief Tests that the KAT evaluation runs once and skips thereafter.
 */
status_t test_stateful_kat_execution(void) {
#ifdef FIPS_MODE
  LOG_INFO("Testing stateful KAT execution for FIPS build using AES...");

  // Verify the state is zeroed out initially
  otcrypto_state_t initial_state = test_cryptolib_state;

  otcrypto_key_config_t config = {
      .version = kOtcryptoLibVersion1,
      .key_mode = kOtcryptoKeyModeAesEcb,
      .key_length = 16,
      .hw_backed = kHardenedBoolFalse,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };

  uint32_t share0_data[4] = {0x01234567, 0x89abcdef, 0x55aa55aa, 0xaa55aa55};
  uint32_t share1_data[4] = {0};
  otcrypto_const_word32_buf_t key_share0 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share0_data, 4);
  otcrypto_const_word32_buf_t key_share1 =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, share1_data, 4);

  uint32_t keyblob[8] = {0};
  otcrypto_blinded_key_t key = {
      .config = config,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  otcrypto_status_t import_status =
      otcrypto_import_blinded_key(&key_share0, &key_share1, &key);
  TRY_CHECK(import_status.value == kHardenedBoolTrue, "Key import failed.");

  uint32_t iv_data[4] = {0};
  otcrypto_word32_buf_t iv =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, iv_data, 4);

  uint8_t input_data[16] = {0};
  otcrypto_const_byte_buf_t input =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, input_data, 16);

  uint8_t output_data[16] = {0};
  otcrypto_byte_buf_t output =
      OTCRYPTO_MAKE_BUF(otcrypto_byte_buf_t, output_data, 16);

  uint64_t t1_start = ibex_mcycle_read();
  otcrypto_status_t status1 =
      otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &input, kOtcryptoAesPaddingNull, &output);
  uint64_t t1_end = ibex_mcycle_read();
  uint64_t first_run_cycles = t1_end - t1_start;

  // Ensure it failed properly inside otcrypto_aes
  TRY_CHECK(status1.value != kHardenedBoolTrue,
            "Expected failure due to mode mismatch.");

  // Verify that some KAT bit was successfully set in our stashed state
  TRY_CHECK(memcmp(&initial_state, &test_cryptolib_state,
                   sizeof(otcrypto_state_t)) != 0,
            "KAT state was not mutated by the cryptolib.");

  uint64_t t2_start = ibex_mcycle_read();
  otcrypto_status_t status2 =
      otcrypto_aes(&key, &iv, kOtcryptoAesModeCbc, kOtcryptoAesOperationEncrypt,
                   &input, kOtcryptoAesPaddingNull, &output);
  uint64_t t2_end = ibex_mcycle_read();
  uint64_t second_run_cycles = t2_end - t2_start;

  TRY_CHECK(status2.value != kHardenedBoolTrue,
            "Expected failure due to mode mismatch.");

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
  // Pass the address of the static state variable
  CHECK_STATUS_OK(
      otcrypto_init(kOtcryptoKeySecurityLevelHigh, &test_cryptolib_state));

  CHECK_STATUS_OK(test_stateful_kat_execution());

  return true;
}
