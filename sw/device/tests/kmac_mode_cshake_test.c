// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

#define DIGEST_LEN_CSHAKE_MAX 4

/**
 * cSHAKE test description.
 */
typedef struct cshake_test {
  dif_kmac_mode_cshake_t mode;

  const char *message;
  size_t message_len;

  const char *function_name;
  size_t function_name_len;

  const char *customization_string;
  size_t customization_string_len;

  const uint32_t digest[DIGEST_LEN_CSHAKE_MAX];
  size_t digest_len;
} cshake_test_t;

/**
 * cSHAKE tests.
 */
const cshake_test_t cshake_tests[] = {
    {
        .mode = kDifKmacModeCshakeLen128,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "",
        .function_name_len = 0,
        .customization_string = "",
        .customization_string_len = 0,
        .digest = {0x235a6522, 0x3bd735ac, 0x77832247, 0xc6b12919},
        .digest_len = 4,  // Rate (r) is 42 words.
    },
    {
        .mode = kDifKmacModeCshakeLen128,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "A",
        .function_name_len = 1,
        .customization_string = "",
        .customization_string_len = 0,
        .digest = {0xf2f20928, 0xa2a59a0, 0xfc1e5d5d, 0x1cee38d0},
        .digest_len = 4,  // Rate (r) is 42 words.
    },
    {
        .mode = kDifKmacModeCshakeLen256,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "",
        .function_name_len = 0,
        .customization_string = "Ibex",
        .customization_string_len = 4,
        .digest = {0xcd582d56, 0x59e88860, 0xa4344c29, 0x5576778f},
        .digest_len = 4,  // Rate (r) is 34 words.
    },
    {
        .mode = kDifKmacModeCshakeLen256,
        .message = "OpenTitan",
        .message_len = 9,
        .function_name = "Ibex",
        .function_name_len = 4,
        .customization_string =
            "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
            "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f",
        .customization_string_len = 32,
        .digest = {0xda353307, 0xdf18e570, 0x6211cee0, 0x716e816c},
        .digest_len = 4,  // Rate (r) is 34 words.
    },
};

bool test_main(void) {
  LOG_INFO("Running KMAC DIF cSHAKE test...");

  // Intialize KMAC hardware.
  dif_kmac_t kmac;
  dif_kmac_operation_state_t kmac_operation_state;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                       0x50dc409c, 0x11e1ebd1},
      .entropy_fast_process = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  // Run cSHAKE test cases using single blocking absorb/squeeze operations.
  for (int i = 0; i < ARRAYSIZE(cshake_tests); ++i) {
    cshake_test_t test = cshake_tests[i];

    dif_kmac_function_name_t n;
    CHECK_DIF_OK(dif_kmac_function_name_init(test.function_name,
                                             test.function_name_len, &n));

    dif_kmac_customization_string_t s;
    CHECK_DIF_OK(dif_kmac_customization_string_init(
        test.customization_string, test.customization_string_len, &s));

    // Use NULL for empty strings to exercise that code path.
    dif_kmac_function_name_t *np = test.function_name_len == 0 ? NULL : &n;
    dif_kmac_customization_string_t *sp =
        test.customization_string_len == 0 ? NULL : &s;

    CHECK_DIF_OK(dif_kmac_mode_cshake_start(&kmac, &kmac_operation_state,
                                            test.mode, np, sp));
    CHECK_DIF_OK(dif_kmac_absorb(&kmac, &kmac_operation_state, test.message,
                                 test.message_len, NULL));
    uint32_t out[DIGEST_LEN_CSHAKE_MAX];
    CHECK(DIGEST_LEN_CSHAKE_MAX >= test.digest_len);
    CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &kmac_operation_state, out,
                                  test.digest_len, /*processed=*/NULL,
                                  /*capacity=*/NULL));
    CHECK_DIF_OK(dif_kmac_end(&kmac, &kmac_operation_state));

    for (int j = 0; j < test.digest_len; ++j) {
      CHECK(out[j] == test.digest[j],
            "test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j],
            test.digest[j]);
    }
  }

  return true;
}
