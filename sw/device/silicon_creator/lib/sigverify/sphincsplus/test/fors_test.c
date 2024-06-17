// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/fors.h"

#include <stdint.h>

#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/hash.h"

OTTF_DEFINE_TEST_CONFIG();

// Test signature, message, and address. Populate before running test.
static uint32_t kTestSig[kSpxForsWords] = {0};
static uint8_t kTestMsg[kSpxForsMsgBytes] = {0};
static spx_addr_t kTestAddr = {.addr = {0}};

// Test context.
static spx_ctx_t kTestCtx = {
    .pub_seed =
        {
            0xf3f2f1f0,
            0xf7f6f5f4,
            0xfbfaf9f8,
            0xfffefdfc,
        },
};

// Test data generated with a third-party implementation of SPHINCS+.
static uint32_t kExpectedPk[kSpxNWords] = {
    0xa8862a36,
    0x193a3511,
    0x4e18a287,
    0xe0006e36,
};

OT_WARN_UNUSED_RESULT
static rom_error_t pk_from_sig_test(void) {
  // Initialize the KMAC block.
  RETURN_IF_ERROR(spx_hash_initialize(&kTestCtx));

  // Extract the public key from the signature.
  uint32_t actual_pk[kSpxNWords];
  fors_pk_from_sig(kTestSig, kTestMsg, &kTestCtx, &kTestAddr, actual_pk);

  // Check results.
  CHECK_ARRAYS_EQ(actual_pk, kExpectedPk, kSpxNWords);
  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Populate signature with {0, 1, 2, 3, ... }.
  unsigned char *test_sig_bytes = (unsigned char *)kTestSig;
  for (size_t i = 0; i < kSpxForsBytes; i++) {
    test_sig_bytes[i] = i & 255;
  }

  // Populate message with { ..., 3, 2, 1, 0}.
  for (size_t i = 0; i < kSpxForsMsgBytes; i++) {
    kTestMsg[i] = (kSpxForsMsgBytes - i) & 255;
  }

  // Populate address.
  spx_addr_layer_set(&kTestAddr, 0xa3);
  spx_addr_tree_set(&kTestAddr, 0xafaeadacabaaa9a8);
  spx_addr_type_set(&kTestAddr, kSpxAddrTypeForsTree);
  spx_addr_keypair_set(&kTestAddr, 0xb4b5b6b7);

  EXECUTE_TEST(result, pk_from_sig_test);

  return status_ok(result);
}
