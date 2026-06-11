// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "third_party/embedpqc/mldsa44_tiny.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/embedpqc/mldsa_test_utils.h"
#include "sw/device/tests/embedpqc/mldsa_testvectors.h"
#include "third_party/embedpqc/ports/mldsa44_tiny_caller.h"

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  LOG_INFO("MLDSA44-TINY Test starting...");

  // Allocate a single static buffer to reuse for all RAM outputs to save BSS
  // space.
  static uint8_t buf[MLDSA44_SIGNATURE_BYTES];

  // 1. Keygen Test
  paint_stack();
  mldsa44_tiny_pub_from_seed_with_stack(buf, kMldsa44KeygenSeed,
                                        &mldsa_stack[MLDSA_STACK_SIZE]);
  size_t keygen_stack = get_max_stack_usage();
  LOG_INFO("mldsa44_tiny_pub_from_seed Max Stack Usage: %u bytes",
           (unsigned int)keygen_stack);

  CHECK(check_arrays_eq_verbose(buf, kMldsa44ExpectedPublicKey,
                                MLDSA44_PUBLIC_KEY_BYTES),
        "PublicKey mismatch!");
  LOG_INFO("Keygen Test Passed.");

  // 2. Sign Test
  paint_stack();
  mldsa44_tiny_sign_deterministic_with_stack(
      buf, kMldsa44KeygenSeed, kMldsa44Message, sizeof(kMldsa44Message),
      &mldsa_stack[MLDSA_STACK_SIZE]);
  size_t sign_stack = get_max_stack_usage();
  LOG_INFO("mldsa44_tiny_sign Max Stack Usage: %u bytes",
           (unsigned int)sign_stack);

  CHECK(check_arrays_eq_verbose(buf, kMldsa44ExpectedSignature,
                                MLDSA44_SIGNATURE_BYTES),
        "Signature mismatch!");
  LOG_INFO("Sign Test Passed.");

  // 3. Verify Test
  paint_stack();
  int verify_res = mldsa44_tiny_verify_with_stack(
      kMldsa44ExpectedPublicKey, kMldsa44ExpectedSignature, kMldsa44Message,
      sizeof(kMldsa44Message), &mldsa_stack[MLDSA_STACK_SIZE]);
  size_t verify_stack = get_max_stack_usage();
  LOG_INFO("mldsa44_tiny_verify Max Stack Usage: %u bytes",
           (unsigned int)verify_stack);

  CHECK(verify_res != 0, "mldsa44_tiny_verify failed!");
  LOG_INFO("Verify Test Passed.");

  LOG_INFO("MLDSA44-TINY Test completed successfully!");
  return true;
}
