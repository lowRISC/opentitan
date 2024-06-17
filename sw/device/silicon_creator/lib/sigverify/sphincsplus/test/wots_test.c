// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/wots.h"

#include <stdint.h>

#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/hash.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/params.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kSpxWotsMsgBytes = ((kSpxWotsLen1 * kSpxWotsLogW + 7) / 8),
  kSpxWotsMsgWords =
      (kSpxWotsMsgBytes + sizeof(uint32_t) - 1) / sizeof(uint32_t),
};

// Test signature, message, and address. Populate before running test.
static uint32_t kTestSig[kSpxWotsWords] = {0};
static uint32_t kTestMsg[kSpxWotsMsgWords] = {0};
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
static uint32_t kExpectedLeaf[kSpxNWords] = {0x14199738, 0x8d0ae722, 0x27ba271f,
                                             0x94194a62};

OT_WARN_UNUSED_RESULT
static rom_error_t pk_from_sig_test(void) {
  RETURN_IF_ERROR(spx_hash_initialize(&kTestCtx));

  // Extract the public key from the signature.
  uint32_t wots_pk[kSpxWotsPkWords];
  wots_pk_from_sig(kTestSig, kTestMsg, &kTestCtx, &kTestAddr, wots_pk);

  // Compute the leaf node using `thash`. This is the next step in the
  // verification procedure and FIPS 205 combines it into the same algorithm as
  // `wots_pk_from_sig`; mostly this lets us have a shorter value to check.
  spx_addr_t wots_pk_addr = {.addr = {0}};
  spx_addr_type_set(&wots_pk_addr, kSpxAddrTypeWotsPk);
  spx_addr_keypair_copy(&wots_pk_addr, &kTestAddr);
  uint32_t actual_leaf[kSpxNWords];
  thash(wots_pk, kSpxWotsLen, &kTestCtx, &wots_pk_addr, actual_leaf);

  // Check results.
  CHECK_ARRAYS_EQ(actual_leaf, kExpectedLeaf, ARRAYSIZE(kExpectedLeaf));

  return kErrorOk;
}

bool test_main(void) {
  status_t result = OK_STATUS();

  // Populate signature with {0, 1, 2, 3, ... }.
  unsigned char *test_sig_bytes = (unsigned char *)kTestSig;
  for (size_t i = 0; i < kSpxWotsBytes; i++) {
    test_sig_bytes[i] = i & 255;
  }

  // Populate message with { ..., 3, 2, 1, 0}.
  unsigned char *test_msg_bytes = (unsigned char *)kTestMsg;
  for (size_t i = 0; i < kSpxWotsMsgBytes; i++) {
    test_msg_bytes[i] = (kSpxWotsMsgBytes - i) & 255;
  }

  // Populate address.
  spx_addr_layer_set(&kTestAddr, 0xa3);
  spx_addr_tree_set(&kTestAddr, 0xafaeadacabaaa9a8);
  spx_addr_type_set(&kTestAddr, kSpxAddrTypeWots);
  spx_addr_keypair_set(&kTestAddr, 0xb4b5b6b7);

  EXECUTE_TEST(result, pk_from_sig_test);

  return status_ok(result);
}
