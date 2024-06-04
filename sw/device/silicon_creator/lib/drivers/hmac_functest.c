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
//     sha256sum - | cut -f1 -d' '  | fold -w2 | tac | tr -d "\n" |
//     sed -e "s/......../0x&,\n/g" | tac
//
static const uint32_t kGettysburgDigest[] = {
    0x03d46f1e, 0xcd34900f, 0xa3085777, 0xed24c396,
    0x87c50e42, 0x33d43deb, 0xc06a9fe2, 0xbac78c8b,
};

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

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, hmac_test);
  return status_ok(result);
}
