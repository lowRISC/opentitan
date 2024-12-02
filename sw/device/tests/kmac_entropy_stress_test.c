// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

#define MIN(a, b) (((a) < (b)) ? (a) : (b))

dif_kmac_config_t kKmacTestCases[] = {

    //////////////////////////////////////////////////////////////////////////////
    // EDN Mode
    //////////////////////////////////////////////////////////////////////////////

    // Entropy wait timer is zero
    {
        .entropy_mode = kDifKmacEntropyModeEdn,
        .entropy_fast_process = false,
        .entropy_hash_threshold = 8,
        .entropy_wait_timer = 0,
        .entropy_prescaler = 0,
    },

    // Entropy wait timer is nonzero
    {
        .entropy_mode = kDifKmacEntropyModeEdn,
        .entropy_fast_process = false,
        .entropy_hash_threshold = 8,
        .entropy_wait_timer = 0xffff,
        .entropy_prescaler = 0x3ff,
    },

    // Entropy refresh hash count is 0 -- expect no hash counter reset
    {
        .entropy_mode = kDifKmacEntropyModeEdn,
        .entropy_fast_process = false,
        .entropy_hash_threshold = 0,
        .entropy_wait_timer = 0,
        .entropy_prescaler = 1,
    },

    // Entropy refresh hash count is 1023, the maximum
    {
        .entropy_mode = kDifKmacEntropyModeEdn,
        .entropy_fast_process = false,
        .entropy_hash_threshold = 1023,
        .entropy_wait_timer = 0,
        .entropy_prescaler = 1,
    },

    //////////////////////////////////////////////////////////////////////////////
    // SW Mode
    //////////////////////////////////////////////////////////////////////////////

    // entropy_hash_threshold = 8; in SW mode, the hash counter will still be
    // reset but entropy will not be refreshed
    {
        .entropy_mode = kDifKmacEntropyModeSoftware,
        .entropy_fast_process = false,
        .entropy_seed =
            {
                0x1234567,
                0x1234567,
                0x1234567,
                0x1234567,
                0x1234567,
            },
        .entropy_hash_threshold = 8,
        .entropy_wait_timer = 0xffff,
        .entropy_prescaler = 0x3ff,
    },

    // entropy_hash_threshold = 0
    {
        .entropy_mode = kDifKmacEntropyModeSoftware,
        .entropy_fast_process = false,
        .entropy_seed =
            {
                0x1234567,
                0x1234567,
                0x1234567,
                0x1234567,
                0x1234567,
            },
        .entropy_hash_threshold = 0,
        .entropy_wait_timer = 0xffff,
        .entropy_prescaler = 0x3ff,
    },
};

enum {
  kKmacDigestLenMax = 100,
  kTestConfigCount = ARRAYSIZE(kKmacTestCases),
  kKmacIterations = 1000,

  // ENTROPY_REFRESH_THRESHOLD_SHADOWED and ENTROPY_REFRESH_HASH_CNT registers
  // are 10 bits wide, so the refresh threshold cannot be set higher and the
  // hash counter cannot count higher than this value
  kHashCntMax = 0x3ff,
};

typedef struct kmac_test_vector {
  dif_kmac_mode_kmac_t mode;
  dif_kmac_key_t key;

  const char *message;
  size_t message_len;

  const char *customization_string;
  size_t customization_string_len;

  const uint32_t digest[kKmacDigestLenMax];
  size_t digest_len;
} kmac_test_vector_t;

/**
 * A single KMAC test vector:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
 */
const kmac_test_vector_t kKmacTestVector = {
    .mode = kDifKmacModeKmacLen256,
    .key =
        (dif_kmac_key_t){
            .share0 = {0x43424140, 0x47464544, 0x4b4a4948, 0x4f4e4f4c,
                       0x53525150, 0x57565554, 0x5b5a5958, 0x5f5e5d5c},
            .share1 = {0},
            .length = kDifKmacKeyLen256,
        },
    .message =
        "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
        "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"
        "\x20\x21\x22\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f"
        "\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f"
        "\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f"
        "\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\x5c\x5d\x5e\x5f"
        "\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\x6f"
        "\x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d\x7e\x7f"
        "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f"
        "\x90\x91\x92\x93\x94\x95\x96\x97\x98\x99\x9a\x9b\x9c\x9d\x9e\x9f"
        "\xa0\xa1\xa2\xa3\xa4\xa5\xa6\xa7\xa8\xa9\xaa\xab\xac\xad\xae\xaf"
        "\xb0\xb1\xb2\xb3\xb4\xb5\xb6\xb7\xb8\xb9\xba\xbb\xbc\xbd\xbe\xbf"
        "\xc0\xc1\xc2\xc3\xc4\xc5\xc6\xc7",
    .message_len = 200,
    .customization_string = "My Tagged Application",
    .customization_string_len = 21,
    .digest = {0x1c73bed5, 0x73d74e95, 0x59bb4628, 0xe3a8e3db, 0x7ae7830f,
               0x5944ff4b, 0xb4c2f1f2, 0xceb8ebec, 0xc601ba67, 0x57b88a2e,
               0x9b492d8d, 0x6727bbd1, 0x90117868, 0x6a300a02, 0x1d28de97,
               0x5d3030cc},
    .digest_len = 16,
};

/**
 * Run many KMAC operations with a particular entropy configuration.
 *
 * This test checks that the KMAC block does not produce any errors and that
 * the hash counter behaves as expected.
 */
status_t test_kmac_config(dif_kmac_config_t *test_case) {
  // The ENTROPY_REFRESH_THRESHOLD_SHADOWED register is 10 bits wide and cannot
  // be set to a value higher than kHashCntMax.
  TRY_CHECK(
      test_case->entropy_hash_threshold <= kHashCntMax,
      "Invalid test case: entropy_hash_threshold too high; greater than %d",
      kHashCntMax);

  dif_kmac_t kmac;
  TRY(dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Handle customization string
  dif_kmac_customization_string_t cust_str;
  TRY(dif_kmac_customization_string_init(
      kKmacTestVector.customization_string,
      kKmacTestVector.customization_string_len, &cust_str));

  // Configure the KMAC block with the config from the test case
  test_case->message_big_endian = false;
  test_case->output_big_endian = false;
  test_case->sideload = false;
  test_case->msg_mask = true;
  TRY(dif_kmac_configure(&kmac, *test_case));

  // Manually clear the hash counter
  uint32_t hash_count, expected_hash_count = 0;
  uint32_t cmd_reg = mmio_region_read32(kmac.base_addr, KMAC_CMD_REG_OFFSET);
  cmd_reg = bitfield_bit32_write(cmd_reg, KMAC_CMD_HASH_CNT_CLR_BIT, 1);
  mmio_region_write32(kmac.base_addr, KMAC_CMD_REG_OFFSET, cmd_reg);
  TRY(dif_kmac_get_hash_counter(&kmac, &hash_count));
  TRY_CHECK(hash_count == 0, "Failed to clear hash counter");

  // Run many KMAC operations
  for (size_t i = 0; i < kKmacIterations; i++) {
    dif_kmac_operation_state_t op_state;
    // Wait for the idle state
    TRY(dif_kmac_poll_status(&kmac, KMAC_STATUS_SHA3_IDLE_BIT));
    TRY(dif_kmac_mode_kmac_start(&kmac, &op_state, kKmacTestVector.mode,
                                 kKmacTestVector.digest_len,
                                 &kKmacTestVector.key, &cust_str));

    TRY(dif_kmac_absorb(&kmac, &op_state, kKmacTestVector.message,
                        kKmacTestVector.message_len,
                        /* processed=*/NULL));

    // All squeeze operations in this test are expected to succeed
    uint32_t out[kKmacDigestLenMax];
    TRY(dif_kmac_squeeze(&kmac, &op_state, out, kKmacTestVector.digest_len,
                         /*processed=*/NULL, /*capacity=*/NULL));

    // Check if the KMAC block is signaling any errors
    bool irq_err_pending;
    TRY(dif_kmac_irq_is_pending(&kmac, kDifKmacIrqKmacErr, &irq_err_pending));

    // If IrqKmacErr is pending, get the error status and abort
    if (irq_err_pending) {
      dif_kmac_error_t err_status;
      TRY(dif_kmac_get_error(&kmac, &err_status, /*info=*/NULL));

      TRY_CHECK(!irq_err_pending, "KMAC error occurred: 0x%x", err_status);
    }

    // Check the hash counter value
    TRY(dif_kmac_get_hash_counter(&kmac, &hash_count));
    if (test_case->entropy_hash_threshold != 0) {
      expected_hash_count =
          (expected_hash_count + 1) % test_case->entropy_hash_threshold;
    } else {
      // If the hash counter threshold is not enabled (i.e. set to 0), the hash
      // counter maxes out at kHashCntMax and should not overflow
      expected_hash_count = MIN(expected_hash_count + 1, kHashCntMax);
    }
    TRY_CHECK(expected_hash_count == hash_count,
              "Unexpected hash counter value: Got %d, Expected %d", hash_count,
              expected_hash_count);

    TRY(dif_kmac_end(&kmac, &op_state));
  }

  return OK_STATUS();
}

status_t test_kmac_entropy_stress(void) {
  LOG_INFO("Running KMAC entropy stress test...");

  for (size_t i = 0; i < kTestConfigCount; i++) {
    LOG_INFO("Running test case %d", i);
    test_kmac_config(&kKmacTestCases[i]);
  }

  LOG_INFO("DONE");
  return OK_STATUS();
}

bool test_main(void) {
  static status_t result;
  EXECUTE_TEST(result, test_kmac_entropy_stress);
  return status_ok(result);
}
