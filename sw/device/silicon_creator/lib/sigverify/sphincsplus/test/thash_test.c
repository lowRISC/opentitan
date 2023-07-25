// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/thash.h"

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/address.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/context.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

static void chain_test(spx_ctx_t *ctx, size_t steps,
                       const spx_addr_t *start_addr,
                       const uint32_t *exp_result) {
  uint32_t out[kSpxNWords] = {0};

  // Copy `start_addr` to a non-constant buffer.
  spx_addr_t addr;
  memcpy(addr.addr, start_addr->addr,
         ARRAYSIZE(start_addr->addr) * sizeof(uint32_t));

  // Perform WOTS-like chaining operation for the specified number of steps.
  for (uint8_t i = 0; i < steps; i++) {
    spx_addr_hash_set(&addr, i);
    CHECK(thash((unsigned char *)out, 1, ctx, &addr, out) == kErrorOk);
  }

  // Check the results if an expected value was given.
  if (exp_result != NULL) {
    CHECK_ARRAYS_EQ(out, exp_result, kSpxNWords);
  }
}

bool test_main() {
  spx_ctx_t ctx = {
      .pub_seed = {0},
  };
  CHECK(kmac_shake256_configure() == kErrorOk);
  LOG_INFO("Setup complete.");

  // Dummy address for testing.
  const spx_addr_t addr = {.addr = {0xdeadbeef}};

  // Test chain of length 3.
  static const uint32_t exp_result3[kSpxNWords] = {0x42021160, 0x96339114,
                                                   0x62a8c829, 0x18b64426};
  chain_test(&ctx, 3, &addr, exp_result3);

  // Test chain of length 10.
  static const uint32_t exp_result10[kSpxNWords] = {0x81e421db, 0xb20b479b,
                                                    0x873f120e, 0x9d4a8558};
  chain_test(&ctx, 10, &addr, exp_result10);

  return true;
}
