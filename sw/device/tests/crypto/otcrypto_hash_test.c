// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// This test checks that the static-linked `otcrypto` library is usable.

// From: http://www.abrahamlincolnonline.org/lincoln/speeches/gettysburg.htm
static const char kGettysburgPrelude[] =
    "Four score and seven years ago our fathers brought forth on this "
    "continent, a new nation, conceived in Liberty, and dedicated to the "
    "proposition that all men are created equal.";

// The following shell command will produce the sha256sum and convert the
// digest into valid C hexadecimal constants:
//
// $ echo -n "Four score and seven years ago our fathers brought forth on this
// continent, a new nation, conceived in Liberty, and dedicated to the
// proposition that all men are created equal." |
//     sha256sum - | cut -f1 -d' ' | sed -e "s/../0x&, /g"
//
static const uint8_t kGettysburgDigest[] = {
    0x1e, 0x6f, 0xd4, 0x03, 0x0f, 0x90, 0x34, 0xcd, 0x77, 0x57, 0x08,
    0xa3, 0x96, 0xc3, 0x24, 0xed, 0x42, 0x0e, 0xc5, 0x87, 0xeb, 0x3d,
    0xd4, 0x33, 0xe2, 0x9f, 0x6a, 0xc0, 0x8b, 0x8c, 0xc7, 0xba,
};

status_t hash_test(void) {
  uint32_t digest_content[8];
  otcrypto_sha2_context_t ctx;
  otcrypto_hash_digest_t digest = {
      .len = ARRAYSIZE(digest_content),
      .data = digest_content,
  };
  otcrypto_const_byte_buf_t buf = {
      .len = sizeof(kGettysburgPrelude) - 1,
      .data = (const uint8_t *)kGettysburgPrelude,
  };

  TRY(otcrypto_sha2_init(kOtcryptoHashModeSha256, &ctx));
  TRY(otcrypto_sha2_update(&ctx, buf));
  TRY(otcrypto_sha2_final(&ctx, &digest));

  TRY_CHECK_ARRAYS_EQ((const uint8_t *)digest.data, kGettysburgDigest,
                      ARRAYSIZE(kGettysburgDigest));
  TRY_CHECK(digest.mode == kOtcryptoHashModeSha256);
  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  result = hash_test();
  return status_ok(result);
}
