// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/ecc/ecdh_p256.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

status_t key_exchange_test(void) {
  // Generate a keypair.
  LOG_INFO("Generating keypair A...");
  TRY(ecdh_p256_keypair_start());
  p256_masked_scalar_t private_keyA;
  p256_point_t public_keyA;
  TRY(ecdh_p256_keypair_finalize(&private_keyA, &public_keyA));

  // Generate a second keypair.
  LOG_INFO("Generating keypair B...");
  TRY(ecdh_p256_keypair_start());
  p256_masked_scalar_t private_keyB;
  p256_point_t public_keyB;
  TRY(ecdh_p256_keypair_finalize(&private_keyB, &public_keyB));

  // Sanity check; public keys should be different from each other.
  CHECK_ARRAYS_NE(public_keyA.x, public_keyB.x, ARRAYSIZE(public_keyA.x));
  CHECK_ARRAYS_NE(public_keyA.y, public_keyB.y, ARRAYSIZE(public_keyA.y));

  // Compute the shared secret from A's side of the computation (using A's
  // private key and B's public key).
  LOG_INFO("Generating shared secret (A)...");
  TRY(ecdh_p256_shared_key_start(&private_keyA, &public_keyB));
  ecdh_p256_shared_key_t shared_keyA;
  TRY(ecdh_p256_shared_key_finalize(&shared_keyA));

  // Compute the shared secret from B's side of the computation (using B's
  // private key and A's public key).
  LOG_INFO("Generating shared secret (B)...");
  TRY(ecdh_p256_shared_key_start(&private_keyB, &public_keyA));
  ecdh_p256_shared_key_t shared_keyB;
  TRY(ecdh_p256_shared_key_finalize(&shared_keyB));

  // Unmask the keys and check that they match.
  uint32_t keyA[ARRAYSIZE(shared_keyA.share0)];
  uint32_t keyB[ARRAYSIZE(keyA)];
  for (size_t i = 0; i < ARRAYSIZE(keyA); i++) {
    keyA[i] = shared_keyA.share0[i] ^ shared_keyA.share1[i];
    keyB[i] = shared_keyB.share0[i] ^ shared_keyB.share1[i];
  }
  CHECK_ARRAYS_EQ(keyA, keyB, ARRAYSIZE(keyA));

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());

  status_t err = key_exchange_test();
  if (!status_ok(err)) {
    // If there was an error, print the OTBN error bits and instruction count.
    LOG_INFO("OTBN error bits: 0x%08x", otbn_err_bits_get());
    LOG_INFO("OTBN instruction count: 0x%08x", otbn_instruction_count_get());
    // Print the error.
    CHECK_STATUS_OK(err);
    return false;
  }

  return true;
}
