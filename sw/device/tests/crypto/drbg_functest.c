// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/randomness_quality.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

OTTF_DEFINE_TEST_CONFIG();

static const uint32_t kTestSeed[12] = {
    0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5, 0xdfec9db3,
    0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c, 0xa468649e, 0xdf5d73fa};
// Note that the word order in the expected output is reversed compared to the
// NIST reference.
static const uint32_t kExpOutput[16] = {
    0xd1c07cd9, 0x5af8a7f1, 0x1012c84c, 0xe48bb8cb, 0x87189e99, 0xd40fccb1,
    0x771c619b, 0xdf82ab22, 0x80b1dc2f, 0x2581f391, 0x64f7ac0c, 0x510494b3,
    0xa43c41b7, 0xdb17514c, 0x87b107ae, 0x793e01c5,
};
static const otcrypto_const_byte_buf_t kEmptyBuffer = {
    .data = NULL,
    .len = 0,
};

static status_t kat_test(void) {
  otcrypto_const_byte_buf_t entropy = {
      .data = (const unsigned char *)kTestSeed,
      .len = sizeof(kTestSeed),
  };

  // Instantiate DRBG.
  TRY(otcrypto_drbg_manual_instantiate(entropy, /*perso_string=*/kEmptyBuffer));

  uint32_t actual_output_words[ARRAYSIZE(kExpOutput)];
  otcrypto_word32_buf_t actual_output = {
      .data = actual_output_words,
      .len = ARRAYSIZE(actual_output_words),
  };

  // Generate output twice.
  LOG_INFO("Generating...");
  TRY(otcrypto_drbg_manual_generate(/*additional_input=*/kEmptyBuffer,
                                    actual_output));
  LOG_INFO("Generating again...");
  TRY(otcrypto_drbg_manual_generate(/*additional_input=*/kEmptyBuffer,
                                    actual_output));

  // Compare second result to expected output.
  TRY_CHECK_ARRAYS_EQ(kExpOutput, actual_output_words, ARRAYSIZE(kExpOutput));
  TRY_CHECK_ARRAYS_EQ(kExpOutput, kExpOutput, 0);

  // Clean up
  TRY(otcrypto_drbg_uninstantiate());

  return OK_STATUS();
}

static status_t random_test(void) {
  // Instantiate DRBG.
  TRY(otcrypto_drbg_instantiate(/*perso_string=*/kEmptyBuffer));

  // Generate a relatively large amount of output data.
  uint32_t output_data[1024];
  otcrypto_word32_buf_t output = {
      .data = output_data,
      .len = ARRAYSIZE(output_data),
  };
  TRY(otcrypto_drbg_generate(/*additional_input=*/kEmptyBuffer, output));

  // Run a basic randomness-quality check on the output.
  status_t res = randomness_quality_monobit_test(
      (unsigned char *)output_data, sizeof(output_data),
      kRandomnessQualitySignificanceOnePercent);

  // Clean up
  TRY(otcrypto_drbg_uninstantiate());

  return res;
}

static status_t reseed_test(void) {
  LOG_INFO("Running reseed and uninstantiate tests...");

  otcrypto_const_byte_buf_t entropy = {
      .data = (const unsigned char *)kTestSeed,
      .len = sizeof(kTestSeed),
  };

  uint8_t add_input_data[16] = {0xAA};
  otcrypto_const_byte_buf_t add_input = {
      .data = add_input_data,
      .len = sizeof(add_input_data),
  };

  // Manual Reseed
  TRY(otcrypto_drbg_manual_instantiate(entropy, kEmptyBuffer));
  TRY(otcrypto_drbg_manual_reseed(entropy, add_input));
  TRY(otcrypto_drbg_uninstantiate());

  // Auto Reseed
  TRY(otcrypto_drbg_instantiate(kEmptyBuffer));
  TRY(otcrypto_drbg_reseed(add_input));
  TRY(otcrypto_drbg_uninstantiate());

  return OK_STATUS();
}

static status_t run_negative_tests(void) {
  LOG_INFO("Running negative tests...");

  otcrypto_const_byte_buf_t valid_entropy = {
      .data = (const unsigned char *)kTestSeed,
      .len = sizeof(kTestSeed),
  };

  uint8_t dummy_data[64] = {0};

  otcrypto_const_byte_buf_t null_data_buf = {.data = NULL, .len = 5};
  otcrypto_const_byte_buf_t too_long_buf = {.data = dummy_data,
                                            .len = 64};  // > kEntropySeedBytes
  otcrypto_const_byte_buf_t bad_len_entropy = {
      .data = dummy_data, .len = 16};  // != kEntropySeedBytes

  uint32_t out_data[4] = {0};
  otcrypto_word32_buf_t valid_out = {.data = out_data, .len = 4};
  otcrypto_word32_buf_t zero_out = {.data = out_data, .len = 0};
  otcrypto_word32_buf_t null_out = {.data = NULL, .len = 4};

  CHECK(otcrypto_drbg_instantiate(null_data_buf).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_instantiate(too_long_buf).value ==
        OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_drbg_reseed(null_data_buf).value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_reseed(too_long_buf).value == OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_drbg_manual_instantiate(valid_entropy, null_data_buf).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_instantiate(null_data_buf, kEmptyBuffer).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_instantiate(bad_len_entropy, kEmptyBuffer).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_instantiate(valid_entropy, too_long_buf).value ==
        OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_drbg_manual_reseed(valid_entropy, null_data_buf).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_reseed(null_data_buf, kEmptyBuffer).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_reseed(bad_len_entropy, kEmptyBuffer).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_reseed(valid_entropy, too_long_buf).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Zero length output
  CHECK(otcrypto_drbg_generate(kEmptyBuffer, zero_out).value ==
        OTCRYPTO_OK.value);
  CHECK(otcrypto_drbg_manual_generate(kEmptyBuffer, zero_out).value ==
        OTCRYPTO_OK.value);

  // Null outputs
  CHECK(otcrypto_drbg_generate(kEmptyBuffer, null_out).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_generate(kEmptyBuffer, null_out).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Null additional input
  CHECK(otcrypto_drbg_generate(null_data_buf, valid_out).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_drbg_manual_generate(null_data_buf, valid_out).value ==
        OTCRYPTO_BAD_ARGS.value);

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the entropy complex.
  CHECK_STATUS_OK(entropy_complex_init());
  CHECK_STATUS_OK(entropy_complex_check());

  EXECUTE_TEST(result, kat_test);
  EXECUTE_TEST(result, random_test);
  EXECUTE_TEST(result, reseed_test);
  EXECUTE_TEST(result, run_negative_tests);

  return status_ok(result);
}
