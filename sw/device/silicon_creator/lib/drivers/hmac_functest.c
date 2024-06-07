// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/hexstr.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

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
//     sha256sum - | cut -f1 -d' ' | sed -e "s/......../0x&,\n/g" | tac
//
static const uint32_t kGettysburgDigest[] = {
    0x8b8cc7ba, 0xe29f6ac0, 0xeb3dd433, 0x420ec587,
    0x96c324ed, 0x775708a3, 0x0f9034cd, 0x1e6fd403,
};

/*
 * For the big-endian version of the test, we use the unmodified output of
 * sha256sum:
 *
 $ echo -n "Four score and seven years ago our fathers brought forth on this\
 continent, a new nation, conceived in Liberty, and dedicated to the\
 proposition that all men are created equal." | sha256sum -

 1e6fd4030f9034cd775708a396c324ed420ec587eb3dd433e29f6ac08b8cc7ba  -
 */
static const char kGettysburgDigestBigEndian[] =
    "1e6fd4030f9034cd775708a396c324ed420ec587eb3dd433e29f6ac08b8cc7ba";

rom_error_t hmac_test(void) {
  hmac_digest_t digest;
  hmac_sha256(kGettysburgPrelude, sizeof(kGettysburgPrelude) - 1, &digest);

  const size_t len = ARRAYSIZE(digest.digest);
  for (int i = 0; i < len; ++i) {
    LOG_INFO("word %d = 0x%08x", i, digest.digest[i]);
    if (digest.digest[i] != kGettysburgDigest[i]) {
      return kErrorUnknown;
    }
  }
  return kErrorOk;
}

rom_error_t hmac_truncated_test(void) {
  uint32_t digest[3];
  hmac_sha256_init();
  hmac_sha256_update(kGettysburgPrelude, sizeof(kGettysburgPrelude) - 1);
  hmac_sha256_final_truncated(digest, ARRAYSIZE(digest));

  const size_t len = ARRAYSIZE(digest);
  for (int i = 0; i < len; ++i) {
    LOG_INFO("word %d = 0x%08x", i, digest[i]);
    if (digest[i] != kGettysburgDigest[i]) {
      return kErrorUnknown;
    }
  }
  return kErrorOk;
}

rom_error_t hmac_bigendian_test(void) {
  uint32_t result[8];
  hexstr_decode(&result, sizeof(result), kGettysburgDigestBigEndian);

  hmac_digest_t digest;
  hmac_sha256_init_endian(true);
  hmac_sha256_update(kGettysburgPrelude, sizeof(kGettysburgPrelude) - 1);
  hmac_sha256_final(&digest);

  const size_t len = ARRAYSIZE(digest.digest);
  for (int i = 0; i < len; ++i) {
    LOG_INFO("word %d = 0x%08x", i, digest.digest[i]);
    if (digest.digest[i] != result[i]) {
      return kErrorUnknown;
    }
  }
  return kErrorOk;
}

rom_error_t hmac_bigendian_truncated_test(void) {
  uint32_t result[8];
  hexstr_decode(&result, sizeof(result), kGettysburgDigestBigEndian);

  hmac_sha256_init_endian(true);
  hmac_sha256_update(kGettysburgPrelude, sizeof(kGettysburgPrelude) - 1);
  uint32_t digest[3];
  hmac_sha256_final_truncated(digest, ARRAYSIZE(digest));

  const size_t len = ARRAYSIZE(digest);
  for (int i = 0; i < len; ++i) {
    LOG_INFO("word %d = 0x%08x", i, digest[i]);
    if (digest[i] != result[i]) {
      return kErrorUnknown;
    }
  }
  return kErrorOk;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, hmac_test);
  EXECUTE_TEST(result, hmac_truncated_test);
  EXECUTE_TEST(result, hmac_bigendian_test);
  EXECUTE_TEST(result, hmac_bigendian_truncated_test);
  return status_ok(result);
}
