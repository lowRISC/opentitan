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

#define DIGEST_LEN_KMAC_MAX 100

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

  const uint32_t digest[DIGEST_LEN_KMAC_MAX];
  size_t digest_len;
  bool digest_len_is_fixed;
} kmac_test_t;

/**
 * KMAC tests.
 *
 * KMAC examples taken from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
 *
 * KMACXOF examples taken from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMACXOF_samples.pdf
 */
const kmac_test_t kmac_tests[] = {
    // KMAC
    {
        .mode = kDifKmacModeKmacLen128,
        .key =
            (dif_kmac_key_t){
                .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C,
                           0x53525150, 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
                .share1 = {0},
                .length = kDifKmacKeyLen256,
            },
        .message = "\x00\x01\x02\x03",
        .message_len = 4,
        .customization_string = "",
        .customization_string_len = 0,
        .digest = {0x0D0B78E5, 0xD3F7A63E, 0x70C529A4, 0x003AA46A, 0xD4D7DBFA,
                   0x9E832896, 0x3F248731, 0x4EE16E45},
        .digest_len = 8,
        .digest_len_is_fixed = true,
    },
    {
        .mode = kDifKmacModeKmacLen256,
        .key =
            (dif_kmac_key_t){
                .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C,
                           0x53525150, 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
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
        .digest = {0xF71886B5, 0xD5E1921F, 0x558C1B6C, 0x18CDD7DD, 0xCAB4978B,
                   0x1E83994D, 0x839A69B2, 0xD9E4A27D, 0xFDACFB70, 0xAE3300E5,
                   0xA2F185A5, 0xC3108570, 0x0888072D, 0x2818BD01, 0x6847FE98,
                   0x6589FC76},
        .digest_len = 16,
        .digest_len_is_fixed = true,
    },
    {
        .mode = kDifKmacModeKmacLen128,
        .key =
            (dif_kmac_key_t){
                .share0 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
                           15},
                .share1 = {0},
                .length = kDifKmacKeyLen512,
            },
        .message = "OpenTitan",
        .message_len = 9,
        .customization_string =
            "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f"
            "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f",
        .customization_string_len = 32,
        .digest = {0x0A77209A, 0x81797CFC, 0x6C6A61AA, 0x87E02697, 0xFC583498,
                   0x924C7FD8, 0xD7E11A80, 0xCEBFD97E, 0x5D01E715, 0xE197129F,
                   0xCED75441, 0x3A08D021, 0xBBACB3CA, 0x353539F9, 0xCD225ACE,
                   0x07C377A5, 0xDEB816E7, 0x6102E338, 0xBA1BA63C, 0x9FD50F0E,
                   0x2B2F632E, 0xABC632E1, 0xF44E5360, 0x01618ABD, 0xCEA93A18,
                   0xA25E1479, 0xACE0387A, 0x8CC8E65A, 0xC5323FBD, 0xCE278A2F,
                   0x6E5C6CD4, 0xDEF0B252, 0xC9569830, 0xDCD1E15A, 0x01592E1D,
                   0x6D41FBEC, 0x7625B67E, 0x2E6FDC71, 0x753253F6, 0xCBE2EE7B,
                   0x94B3F8AB, 0x5F7B9F4B, 0x9C32B704, 0xB75D2CD2, 0x2B9BF8D5,
                   0xF0C43941, 0x070A972F, 0x29039D89, 0x985B43BE, 0x3739526F,
                   0xEB9DE9FE, 0xE885D4EB, 0x147B854A, 0xF39840A4, 0x927FCEEF,
                   0xAA41A128, 0xBF85C5C4, 0x492D7E2B, 0xC39FC808, 0x260A3D02,
                   0x0EAB74F2, 0xFE7B8A99, 0xF77C71F7, 0x49D69382, 0x7B8405D4,
                   0x3D55F0F9, 0x551EAD0B, 0x53D648D0, 0x1820BAEB, 0x8D94C965,
                   0x079BC208, 0xD4D2742F, 0x8496D429, 0x464B6D3A, 0x34899027,
                   0x940B6F55, 0x154F43FB, 0x8C39F574, 0x89E07C5F, 0xE10F713B,
                   0x8B638E35, 0x16F0BFCE, 0x21CB26F8, 0x0A25F977, 0xAD944F1B,
                   0x6B8A6DB7, 0x0ABD1C91, 0x18E2C5AF, 0xE9AF73F5, 0x79CD8C86,
                   0x6830AD6F, 0x9EA2CC45, 0xA70D1807, 0x38993A63, 0xC2BF657E,
                   0x7CE11825, 0x98774D38, 0x9DB867E7, 0xB5F8CBFB, 0x86B242D5},
        .digest_len = 100,
        .digest_len_is_fixed = true,
    },
    // KMACXOF
    {
        .mode = kDifKmacModeKmacLen128,
        .key =
            (dif_kmac_key_t){
                .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C,
                           0x53525150, 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
                .share1 = {0},
                .length = kDifKmacKeyLen256,
            },
        .message = "\x00\x01\x02\x03",
        .message_len = 4,
        .customization_string = "",
        .customization_string_len = 0,
        .digest = {0x0B7483CD, 0xC8CC92BD, 0x142B03CF, 0x46F4A081, 0xDDA97C0E,
                   0x0C8AB012, 0x8B173140, 0x35ECD6AC},
        .digest_len = 8,
        .digest_len_is_fixed = false,
    },
    {
        .mode = kDifKmacModeKmacLen256,
        .key =
            (dif_kmac_key_t){
                .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C,
                           0x53525150, 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
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
        .digest = {0x1C73BED5, 0x73D74E95, 0x59BB4628, 0xE3A8E3DB, 0x7AE7830F,
                   0x5944FF4B, 0xB4C2F1F2, 0xCEB8EBEC, 0xC601BA67, 0x57B88A2E,
                   0x9B492D8D, 0x6727BBD1, 0x90117868, 0x6A300A02, 0x1D28DE97,
                   0x5D3030CC},
        .digest_len = 16,
        .digest_len_is_fixed = false,
    },
};

bool test_main(void) {
  LOG_INFO("Running KMAC DIF test...");

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

  // Run fixed length KMAC test cases using single blocking absorb/squeeze
  // operations.
  for (int i = 0; i < ARRAYSIZE(kmac_tests); ++i) {
    kmac_test_t test = kmac_tests[i];

    dif_kmac_customization_string_t s;
    CHECK_DIF_OK(dif_kmac_customization_string_init(
        test.customization_string, test.customization_string_len, &s));

    // Use NULL for empty strings to exercise that code path.
    dif_kmac_customization_string_t *sp =
        test.customization_string_len == 0 ? NULL : &s;

    size_t l = test.digest_len_is_fixed ? test.digest_len : 0;
    CHECK_DIF_OK(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                                          test.mode, l, &test.key, sp));
    CHECK_DIF_OK(dif_kmac_absorb(&kmac, &kmac_operation_state, test.message,
                                 test.message_len, NULL));
    uint32_t out[DIGEST_LEN_KMAC_MAX];
    CHECK(DIGEST_LEN_KMAC_MAX >= test.digest_len);
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
