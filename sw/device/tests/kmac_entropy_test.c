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

OTTF_DEFINE_TEST_CONFIG();

/**
 * Struct to pack timeout values.
 */
typedef struct kmac_edn_timeout {
  uint16_t prescaler;
  uint16_t wait_timer;
  // Whether we expect timeout for hard-coded (`prescaler`, `wait_timer`) pairs
  bool timeout_expected;
} kmac_edn_timeout_t;

/**
 * Define various timer values to be used in the test.
 */
static const kmac_edn_timeout_t kTestTimeoutVals[] = {
    {
        .prescaler = 0x000,
        .wait_timer = 0x0001,
        .timeout_expected = true,
    },
    {
        .prescaler = 0x000,
        .wait_timer = 0x0001,
        .timeout_expected = true,
    },
    {
        .prescaler = 0x3ff,
        .wait_timer = 0xffff,
        .timeout_expected = false,
    },
    {
        .prescaler = 0x3ff,
        .wait_timer = 0xffff,
        .timeout_expected = false,
    },
};

enum {
  kKmacTimeoutTestCount = ARRAYSIZE(kTestTimeoutVals),
  // Maxiumum digest size in bytes
  kKmacDigestLenMax = 100,
};

/**
 * KMAC test description.
 */
typedef struct kmac_test {
  dif_kmac_mode_kmac_t mode;
  dif_kmac_key_t key;

  const char *message;
  size_t message_len;

  const char *customization_string;
  size_t customization_string_len;

  const uint32_t digest[kKmacDigestLenMax];
  size_t digest_len;
  bool digest_len_is_fixed;
} kmac_test_t;

/**
 * A single KMAC example:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
 */
const kmac_test_t kKmacTestVector = {
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
    .digest_len_is_fixed = false,
};

bool test_main(void) {
  LOG_INFO("Running KMAC ENTROPY test...");

  // Initialize KMAC HWIP
  dif_kmac_t kmac;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC to use EDN entropy
  dif_kmac_config_t config = {
      .entropy_mode = kDifKmacEntropyModeEdn,
      .entropy_fast_process = false,
      // In the last iteration, we expect to see that hash_ctr rewinds to 0
      .entropy_hash_threshold = kKmacTimeoutTestCount,
      .message_big_endian = false,
      .output_big_endian = false,
      .sideload = false,
      .msg_mask = false,
  };

  // Handle string encoding
  dif_kmac_customization_string_t str_buffer;
  CHECK_DIF_OK(dif_kmac_customization_string_init(
      kKmacTestVector.customization_string,
      kKmacTestVector.customization_string_len, &str_buffer));

  // When customization_string is empty, use NULL to activate empty str path
  dif_kmac_customization_string_t *str_buffer_ptr =
      kKmacTestVector.customization_string_len == 0 ? NULL : &str_buffer;

  size_t test_digest_len =
      kKmacTestVector.digest_len_is_fixed ? kKmacTestVector.digest_len : 0;

  for (size_t i = 0; i < kKmacTimeoutTestCount; ++i) {
    LOG_INFO("loop_ctr = %d", i);

    kmac_edn_timeout_t timeout_test = kTestTimeoutVals[i];

    config.entropy_prescaler = timeout_test.prescaler;
    config.entropy_wait_timer = timeout_test.wait_timer;

    CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

    dif_kmac_operation_state_t kmac_operation_state;
    CHECK_DIF_OK(dif_kmac_mode_kmac_start(
        &kmac, &kmac_operation_state, kKmacTestVector.mode, test_digest_len,
        &kKmacTestVector.key, str_buffer_ptr));

    CHECK_DIF_OK(dif_kmac_absorb(&kmac, &kmac_operation_state,
                                 kKmacTestVector.message,
                                 kKmacTestVector.message_len, NULL));

    CHECK(kKmacDigestLenMax >= kKmacTestVector.digest_len);

    // This is where timeout might happen, so we handle dif return manually
    uint32_t out[kKmacDigestLenMax];
    dif_result_t res = dif_kmac_squeeze(&kmac, &kmac_operation_state, out,
                                        kKmacTestVector.digest_len,
                                        /*processed=*/NULL, /*capacity=*/NULL);

    // It is OK to get kDifError at this point because of possible timeout
    CHECK(res == kDifOk || res == kDifError);

    // Check if there is a new error
    bool irq_err_pending;
    CHECK_DIF_OK(
        dif_kmac_irq_is_pending(&kmac, kDifKmacIrqKmacErr, &irq_err_pending));
    if (irq_err_pending) {
      dif_kmac_error_t err_status;
      uint32_t err_info;
      CHECK_DIF_OK(dif_kmac_get_error(&kmac, &err_status, &err_info));
      CHECK(err_status == kDifErrorEntropyWaitTimerExpired,
            "Error other than EDN timeout occurred.");
      LOG_INFO("EDN timed out.");
    } else {
      LOG_INFO("EDN seed received before timeout.");
    }

    // At this point, irq_err_pending says if timeout is observed
    CHECK(irq_err_pending == timeout_test.timeout_expected,
          "EDN timeout expectation doesn't match observation.");

    // Flush out the result and check correctness
    CHECK_DIF_OK(dif_kmac_end(&kmac, &kmac_operation_state));

    // If err interrupt is generated, we need clean-up
    if (irq_err_pending) {
      // Clean INTR_STATE
      CHECK_DIF_OK(dif_kmac_irq_acknowledge_all(&kmac));

      // Reset FSM by setting `err_processed` bit
      CHECK_DIF_OK(dif_kmac_reset(&kmac, &kmac_operation_state));

      // At this point, we expect that there are no remaining interrupts.
      dif_kmac_irq_state_snapshot_t intr_snapshot;
      CHECK_DIF_OK(dif_kmac_irq_get_state(&kmac, &intr_snapshot));
      CHECK(intr_snapshot == 0,
            "INTR_STATE is non-zero after timeout clean-up.");

      bool is_kmac_locked;
      CHECK_DIF_OK(dif_kmac_config_is_locked(&kmac, &is_kmac_locked));
      CHECK(!is_kmac_locked, "KMAC still locked after timeout clean-up.");
    }

    // We check whether hash counter is increasing/rewinding as expected
    uint32_t hash_ctr;
    CHECK_DIF_OK(dif_kmac_get_hash_counter(&kmac, &hash_ctr));
    CHECK(hash_ctr == (i + 1) % (kKmacTimeoutTestCount),
          "Hash counter increment is wrong.");
    LOG_INFO("hash_ctr = %d", hash_ctr);
  }

  return true;
}
