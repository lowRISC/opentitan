// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

/**
 * Digest lengths in bytes.
 */
#define DIGEST_LEN_SHA3_224 (224 / 8)
#define DIGEST_LEN_SHA3_256 (256 / 8)
#define DIGEST_LEN_SHA3_384 (384 / 8)
#define DIGEST_LEN_SHA3_512 (512 / 8)
#define DIGEST_LEN_SHA3_MAX DIGEST_LEN_SHA3_512

/**
 * SHA-3 test description.
 */
typedef struct sha3_test {
  dif_kmac_mode_sha3_t mode;

  const char *message;
  size_t message_len;

  const char *digest;
  size_t digest_len;
} sha3_test_t;

/**
 * SHA-3 tests.
 */
const sha3_test_t sha3_tests[] = {
    // Examples taken from NIST FIPS-202 Algorithm Test Vectors:
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
    {
        .mode = kDifKmacModeSha3Len224,
        .message = NULL,
        .message_len = 0,
        .digest = "\x6b\x4e\x03\x42\x36\x67\xdb\xb7\x3b\x6e\x15\x45\x4f\x0e\xb1"
                  "\xab\xd4\x59\x7f\x9a\x1b\x07\x8e\x3f\x5b\x5a\x6b\xc7",
        .digest_len = DIGEST_LEN_SHA3_224,
    },
    {
        .mode = kDifKmacModeSha3Len256,
        .message = "\xe7\x37\x21\x05",
        .message_len = 4,
        .digest =
            "\x3a\x42\xb6\x8a\xb0\x79\xf2\x8c\x4c\xa3\xc7\x52\x29\x6f\x27\x90"
            "\x06\xc4\xfe\x78\xb1\xeb\x79\xd9\x89\x77\x7f\x05\x1e\x40\x46\xae",
        .digest_len = DIGEST_LEN_SHA3_256,
    },
    {
        .mode = kDifKmacModeSha3Len384,
        .message = "\xa7\x48\x47\x93\x0a\x03\xab\xee\xa4\x73\xe1\xf3\xdc\x30"
                   "\xb8\x88\x15",
        .message_len = 17,
        .digest =
            "\xdb\xa6\xf9\x29\xfe\x55\xf9\xd6\x6c\x5f\x67\xc0\xaf\x3b\x82\xf1"
            "\x7b\xcf\x58\xb3\x67\x52\xf3\x16\x5c\x16\x08\x3f\xea\x8f\xd4\x78"
            "\xee\x69\x03\xf2\x7f\x82\x0a\xd2\xdd\x99\x50\xaf\xb4\x8c\x67\x00",
        .digest_len = DIGEST_LEN_SHA3_384,
    },
    {
        .mode = kDifKmacModeSha3Len512,
        .message =
            "\x66\x4e\xf2\xe3\xa7\x05\x9d\xaf\x1c\x58\xca\xf5\x20\x08\xc5\x22"
            "\x7e\x85\xcd\xcb\x83\xb4\xc5\x94\x57\xf0\x2c\x50\x8d\x4f\x4f\x69"
            "\xf8\x26\xbd\x82\xc0\xcf\xfc\x5c\xb6\xa9\x7a\xf6\xe5\x61\xc6\xf9"
            "\x69\x70\x00\x52\x85\xe5\x8f\x21\xef\x65\x11\xd2\x6e\x70\x98\x89"
            "\xa7\xe5\x13\xc4\x34\xc9\x0a\x3c\xf7\x44\x8f\x0c\xae\xec\x71\x14"
            "\xc7\x47\xb2\xa0\x75\x8a\x3b\x45\x03\xa7\xcf\x0c\x69\x87\x3e\xd3"
            "\x1d\x94\xdb\xef\x2b\x7b\x2f\x16\x88\x30\xef\x7d\xa3\x32\x2c\x3d"
            "\x3e\x10\xca\xfb\x7c\x2c\x33\xc8\x3b\xbf\x4c\x46\xa3\x1d\xa9\x0c"
            "\xff\x3b\xfd\x4c\xcc\x6e\xd4\xb3\x10\x75\x84\x91\xee\xba\x60\x3a"
            "\x76",
        .message_len = 145,
        .digest =
            "\xe5\x82\x5f\xf1\xa3\xc0\x70\xd5\xa5\x2f\xbb\xe7\x11\x85\x4a\x44"
            "\x05\x54\x29\x5f\xfb\x7a\x79\x69\xa1\x79\x08\xd1\x01\x63\xbf\xbe"
            "\x8f\x1d\x52\xa6\x76\xe8\xa0\x13\x7b\x56\xa1\x1c\xdf\x0f\xfb\xb4"
            "\x56\xbc\x89\x9f\xc7\x27\xd1\x4b\xd8\x88\x22\x32\x54\x9d\x91\x4e",
        .digest_len = DIGEST_LEN_SHA3_512,
    },
};

bool test_main() {
  LOG_INFO("Running KMAC DIF test...");

  // Intialize KMAC hardware.
  dif_kmac_t kmac;
  CHECK(dif_kmac_init((dif_kmac_params_t){.base_addr = mmio_region_from_addr(
                                              TOP_EARLGREY_KMAC_BASE_ADDR)},
                      &kmac) == kDifKmacOk);

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = 0xffff,
      .entropy_fast_process = kDifKmacToggleEnabled,
      .message_endianness = kDifKmacEndiannessLittle,
      .output_state_endianness = kDifKmacEndiannessLittle,
  };
  CHECK(dif_kmac_configure(&kmac, config) == kDifKmacConfigureOk);

  // Run SHA-3 test cases using blocking absorb/squeeze operations.
  for (int i = 0; i < ARRAYSIZE(sha3_tests); ++i) {
    sha3_test_t test = sha3_tests[i];

    CHECK(dif_kmac_mode_sha3_start(&kmac, test.mode) == kDifKmacConfigureOk);
    if (test.message_len > 0) {
      CHECK(dif_kmac_absorb(&kmac, test.message, test.message_len, NULL) ==
            kDifKmacAbsorbOk);
    }
    uint8_t out[DIGEST_LEN_SHA3_MAX];
    CHECK(DIGEST_LEN_SHA3_MAX >= test.digest_len);
    CHECK(dif_kmac_squeeze(&kmac, out, test.digest_len, NULL) ==
          kDifKmacSqueezeOk);
    CHECK(dif_kmac_end(&kmac) == kDifKmacOk);

    for (int j = 0; j < test.digest_len; ++j) {
      CHECK(out[j] == test.digest[j],
            "test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j],
            test.digest[j]);
    }
  }

  return true;
}
