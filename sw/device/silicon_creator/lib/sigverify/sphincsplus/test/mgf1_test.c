// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/sha2.h"

OTTF_DEFINE_TEST_CONFIG();

// Length of runtime input and output for SPX+ verify with sha2-128s parameter
// set.
enum {
  kMgf1OutputWords = 8,
  kMgf1InputWords = 16,
};

// Test input, same length as runtime input for SPX+ verify.
static const uint32_t kTestInput[kMgf1InputWords] = {
    0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514,
    0x1b1a1918, 0x1f1e1d1c, 0x23222120, 0x27262524, 0x2b2a2928, 0x2f2e2d2c,
    0x33323130, 0x37363534, 0x3b3a3938, 0x3f3e3d3c,
};

// Expected result, generated with PyCryptoDome as follows:
// >>> from Crypto.Signature.pss import MGF1
// >>> from Crypto.Hash import SHA256
// >>> x = bytearray([i for i in range(0x40)])
// >>> MGF1(x, 32, SHA256).hex()
// '926a33148745e412d1b93cfd3829786181935e93ebabb9ae5d42222fd2dfc8a2'
static const uint32_t kExpectedOutput[kMgf1OutputWords] = {
    0x14336a92, 0x12e44587, 0xfd3cb9d1, 0x61782938,
    0x935e9381, 0xaeb9abeb, 0x2f22425d, 0xa2c8dfd2,
};

OT_WARN_UNUSED_RESULT
static rom_error_t mgf1_test(void) {
  uint32_t actual_output[kMgf1OutputWords];
  mgf1_sha256(kTestInput, ARRAYSIZE(kTestInput), ARRAYSIZE(actual_output),
              actual_output);
  CHECK_ARRAYS_EQ(actual_output, kExpectedOutput, ARRAYSIZE(kExpectedOutput));
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();
  EXECUTE_TEST(result, mgf1_test);
  return status_ok(result);
}
