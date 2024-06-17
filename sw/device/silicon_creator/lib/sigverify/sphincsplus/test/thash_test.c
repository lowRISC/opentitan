// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"

#include <stdint.h>

#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/hash.h"

OTTF_DEFINE_TEST_CONFIG();

// Test message. Size should always be a multiple of kSpxNWords.
static uint32_t kTestMsg[2 * kSpxNWords] = {
    0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c,
    0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c,
};

// Test context.
static spx_ctx_t kTestCtx = {
    .pub_seed =
        {
            0x23222120,
            0x27262524,
            0x2b2a2928,
            0x2f2e2d2c,
        },
};

// Test address. Populate before using.
static spx_addr_t kTestAddr = {.addr = {0}};

// This test data was generated using a third-party implementation of SPHINCS+
// (slh-dsa-py).
static uint32_t kExpectedResult[kSpxNWords] = {
    0x3ea2808a,
    0x090d2a51,
    0x9193afcc,
    0x93a58ed8,
};

OT_WARN_UNUSED_RESULT
static rom_error_t thash_test(void) {
  RETURN_IF_ERROR(spx_hash_initialize(&kTestCtx));

  size_t msg_blocks = sizeof(kTestMsg) / kSpxN;
  uint32_t result[kSpxNWords];
  thash(kTestMsg, msg_blocks, &kTestCtx, &kTestAddr, result);

  CHECK_ARRAYS_EQ(result, kExpectedResult, kSpxNWords);
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  spx_addr_layer_set(&kTestAddr, 0xa3);
  spx_addr_tree_set(&kTestAddr, 0xafaeadacabaaa9a8);
  spx_addr_type_set(&kTestAddr, kSpxAddrTypeForsTree);
  spx_addr_keypair_set(&kTestAddr, 0xb4b5b6b7);

  EXECUTE_TEST(result, thash_test);
  return status_ok(result);
}
