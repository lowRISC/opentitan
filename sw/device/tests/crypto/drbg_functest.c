// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/include/drbg.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

OTTF_DEFINE_TEST_CONFIG();

static uint32_t kTestSeed[12] = {
    0x73bec010, 0x9262474c, 0x16a30f76, 0x531b51de, 0x2ee494e5, 0xdfec9db3,
    0xcb7a879d, 0x5600419c, 0xca79b0b0, 0xdda33b5c, 0xa468649e, 0xdf5d73fa};
// Note that the word order in the expected output is reversed compared to the
// NIST reference.
static uint32_t kExpOutput[16] = {
    0xd1c07cd9, 0x5af8a7f1, 0x1012c84c, 0xe48bb8cb, 0x87189e99, 0xd40fccb1,
    0x771c619b, 0xdf82ab22, 0x80b1dc2f, 0x2581f391, 0x64f7ac0c, 0x510494b3,
    0xa43c41b7, 0xdb17514c, 0x87b107ae, 0x793e01c5,
};
static const crypto_uint8_buf_t kEmptyBuffer = {
    .data = NULL,
    .len = 0,
};

static status_t entropy_complex_init_test(void) {
  // This initialization should happen in ROM_EXT, so there is no public API
  // for it in cryptolib.
  TRY(entropy_complex_init());

  // Check the configuration.
  return entropy_complex_check();
}

static status_t kat_test(void) {
  crypto_uint8_buf_t entropy = {
      .data = (unsigned char *)kTestSeed,
      .len = sizeof(kTestSeed),
  };

  // Instantiate DRBG.
  TRY(otcrypto_drbg_manual_instantiate(entropy, /*perso_string=*/kEmptyBuffer));

  uint32_t actual_output_words[ARRAYSIZE(kExpOutput)];
  crypto_uint8_buf_t actual_output = {
      .data = (unsigned char *)actual_output_words,
      .len = sizeof(actual_output_words),
  };

  // Generate output twice.
  LOG_INFO("Generating...");
  TRY(otcrypto_drbg_generate(/*additional_input=*/kEmptyBuffer,
                             sizeof(kExpOutput), &actual_output));
  LOG_INFO("Generating again...");
  TRY(otcrypto_drbg_generate(/*additional_input=*/kEmptyBuffer,
                             sizeof(kExpOutput), &actual_output));

  // Compare second result to expected output.
  TRY_CHECK_ARRAYS_EQ(kExpOutput, actual_output_words, ARRAYSIZE(kExpOutput));
  TRY_CHECK_ARRAYS_EQ(kExpOutput, kExpOutput, 0);

  return OK_STATUS();
}

bool test_main(void) {
  status_t result = OK_STATUS();

  EXECUTE_TEST(result, entropy_complex_init_test);
  EXECUTE_TEST(result, kat_test);
  return status_ok(result);
}
