
// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/crypto/rsa_3072/rsa_3072_verify.h"

// A test vector for RSA-3072 verify (message hashed with SHA-256)
typedef struct rsa_3072_verify_test_vector_t {
  rsa_3072_public_key_t publicKey;  // The public key
  rsa_3072_int_t signature;         // The signature to verify
  char *msg;                        // The message
  size_t msgLen;                    // Length (in bytes) of the message
  bool valid;                       // Expected result (true if signature valid)
  char *comment;                    // Any notes about the test vector
} rsa_3072_verify_test_vector_t;

static const size_t RSA_3072_VERIFY_NUM_TESTS = 0;

static const rsa_3072_verify_test_vector_t rsa_3072_verify_tests[0];
