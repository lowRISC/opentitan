// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/hexstr.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Test data: short message with short output.
 */
static const char short_msg[] = "Test message!";
static const size_t short_msg_len = 13;
static const uint32_t short_msg_digest[8] = {
    0x84f1c984, 0x7a0316bb, 0xe404cfed, 0x83f9078a,
    0x21491adc, 0xd6c30988, 0xc6822ff6, 0x20b73405,
};

/**
 * Test data: long message with long output.
 */
static const char long_msg[] =
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuv"
    "wxyzABCDEFGHIJKLMNOPQRSTUVWXYZ";
static const size_t long_msg_len = 26 * 4;
static const uint32_t long_msg_digest[75] = {
    0x262992ca, 0xe4790cf1, 0x7681c77f, 0xa5366b52, 0x86490a2f, 0xf072d4c9,
    0xd4ea499a, 0x7a192fd2, 0xe1156b59, 0xb8f00ad5, 0x2ff4ba7c, 0xdec27032,
    0x33624f74, 0x88836d86, 0x4c3c6982, 0xb9e841e1, 0x78acb95a, 0x0bdbc7bc,
    0xfddfb2b5, 0x341b7524, 0x0f348bd8, 0x72b689c2, 0xd00a6e55, 0xbac16e94,
    0x5f736b17, 0xce6c5d57, 0x1fa14eb8, 0xced894a2, 0x438c5219, 0xe9eda7a1,
    0x772984f0, 0xea524c61, 0x99f75a75, 0x0ea04b06, 0x0e45a0f8, 0xf4848bd3,
    0x603d42ab, 0xd1994325, 0x5b93f17b, 0x7a88fc50, 0x469bae3b, 0x7ca37e79,
    0xb14209b8, 0x2a7b76f4, 0x434030f5, 0x7ecb89a1, 0x7ec91dfc, 0x2c58d145,
    0x8057038c, 0xbf5961fd, 0xe7b8ec78, 0x719bcc86, 0x60cb10cb, 0x35e2cb69,
    0xa6e9b0c3, 0x3f40cca6, 0x0df368d1, 0x9b122f5b, 0x63c9e1be, 0x58a9070d,
    0x384dafe8, 0x87c4e8f7, 0x5a8c247e, 0x8862d6fa, 0x3a1dd9e8, 0x6fbd6519,
    0x4c2f5eb7, 0x1358ac89, 0x0f9c5541, 0xfc98c30f, 0x15395844, 0x21e7e2d2,
    0x422b1325, 0xc1f9f225, 0x8951c775,
};

rom_error_t shake256_test(size_t input_len, const char *input,
                          size_t output_len, const uint32_t *exp_output) {
  LOG_INFO("Running SHAKE-256 with input len %d and output len %d...",
           input_len, output_len);

  RETURN_IF_ERROR(kmac_shake256_start());

  // Absorb in two steps.
  kmac_shake256_absorb((unsigned char *)input, input_len / 2);
  kmac_shake256_absorb((unsigned char *)&input[input_len / 2],
                       input_len - (input_len / 2));

  // Squeeze output.
  uint32_t act_output[output_len];
  kmac_shake256_squeeze_start();
  RETURN_IF_ERROR(kmac_shake256_squeeze_end(act_output, output_len));

  // Check output matches expectations.
  CHECK_ARRAYS_EQ(act_output, exp_output, output_len);

  return kErrorOk;
}

rom_error_t kmac_shake256_test(void) {
  // Configure KMAC to run SHAKE-256.
  RETURN_IF_ERROR(kmac_shake256_configure());

  // Simple test.
  RETURN_IF_ERROR(shake256_test(short_msg_len, short_msg,
                                ARRAYSIZE(short_msg_digest), short_msg_digest));

  // Test with long input, short output.
  RETURN_IF_ERROR(shake256_test(long_msg_len, long_msg, 1, long_msg_digest));

  // Test with long input, long output.
  RETURN_IF_ERROR(shake256_test(long_msg_len, long_msg,
                                ARRAYSIZE(long_msg_digest), long_msg_digest));

  return kErrorOk;
}

#define KMAC_KMAC256_KAT(name_, prefix_, key_, msg_, rsp_)       \
  status_t kmac_kmac256_kat_##name_(void) {                      \
    /* Constants for this test. */                               \
    const char key_hex[] = key_;                                 \
    const char msg_hex[] = msg_;                                 \
    const char rsp_hex[] = rsp_;                                 \
    const char prefix[] = prefix_;                               \
                                                                 \
    /* Decode constants from hex into local buffers. */          \
    uint32_t key[sizeof(key_hex) / 2 / sizeof(uint32_t)];        \
    uint32_t msg[sizeof(msg_hex) / 2 / sizeof(uint32_t)];        \
    uint32_t rsp[sizeof(rsp_hex) / 2 / sizeof(uint32_t)];        \
    uint32_t output[sizeof(rsp_hex) / 2 / sizeof(uint32_t)];     \
                                                                 \
    TRY(hexstr_decode(key, sizeof(key), key_hex));               \
    TRY(hexstr_decode(msg, sizeof(msg), msg_hex));               \
    TRY(hexstr_decode(rsp, sizeof(rsp), rsp_hex));               \
                                                                 \
    /* Set up KMAC for KMAC-256 with a software provided key. */ \
    TRY(kmac_kmac256_sw_configure());                            \
    TRY(kmac_kmac256_sw_key(key, ARRAYSIZE(key)));               \
    kmac_kmac256_set_prefix(prefix, sizeof(prefix) - 1);         \
                                                                 \
    /* Peform the operation. */                                  \
    TRY(kmac_kmac256_start());                                   \
    kmac_kmac256_absorb(msg, sizeof(msg));                       \
    TRY(kmac_kmac256_final(output, ARRAYSIZE(output)));          \
                                                                 \
    /* Check the result. */                                      \
    CHECK_ARRAYS_EQ(output, rsp, ARRAYSIZE(rsp));                \
    return OK_STATUS();                                          \
  }

// NIST test vectors for KMAC.
// See also: //hw/dv/sv/test_vectors/vectors/xof/kmac/KMAC256Ex1.rsp.
KMAC_KMAC256_KAT(
    /*name=*/1,
    /*prefix=*/"My Tagged Application",
    /*key=*/"404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f",
    /*msg=*/"00010203",
    /*rsp=*/
    "20c570c31346f703c9ac36c61c03cb64c3970d0cfc787e9b79599d273a68d2f7f69d4cc3de"
    "9d104a351689f27cf6f5951f0103f33f4f24871024d9c27773a8dd")

KMAC_KMAC256_KAT(
    /*name=*/2,
    /*prefix=*/"",
    /*key=*/"404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f",
    /*msg=*/
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021222324"
    "25262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40414243444546474849"
    "4a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e"
    "6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f90919293"
    "9495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8"
    "b9babbbcbdbebfc0c1c2c3c4c5c6c7",
    /*rsp=*/
    "75358cf39e41494e949707927cee0af20a3ff553904c86b08f21cc414bcfd691589d27cf5e"
    "15369cbbff8b9a4c2eb17800855d0235ff635da82533ec6b759b69")

KMAC_KMAC256_KAT(
    /*name=*/3,
    /*prefix=*/"My Tagged Application",
    /*key=*/"404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f",
    /*msg=*/
    "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f2021222324"
    "25262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f40414243444546474849"
    "4a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e"
    "6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f90919293"
    "9495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8"
    "b9babbbcbdbebfc0c1c2c3c4c5c6c7",
    /*rsp=*/
    "b58618f71f92e1d56c1b8c55ddd7cd188b97b4ca4d99831eb2699a837da2e4d970fbacfde5"
    "0033aea585f1a2708510c32d07880801bd182898fe476876fc8965")

bool test_main(void) {
  // Disable all entropy. The test should also succeed with entropy enabled,
  // but KMAC blocking on entropy for SHAKE-256 would be unexpected and
  // potentially dangerous behavior for ROM. We disable it here so that if
  // that's happening the test will fail.
  CHECK_STATUS_OK(entropy_testutils_stop_all());

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, kmac_shake256_test);
  EXECUTE_TEST(result, kmac_kmac256_kat_1);
  EXECUTE_TEST(result, kmac_kmac256_kat_2);
  EXECUTE_TEST(result, kmac_kmac256_kat_3);
  return status_ok(result);
}
