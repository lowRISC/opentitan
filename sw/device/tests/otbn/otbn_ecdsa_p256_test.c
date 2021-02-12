// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/otbn.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * ECDSA sign and verify test with the NIST P-256 curve using OTBN.
 *
 * IMPORTANT: This test is not a secure, complete, or reusable implementation of
 * a cryptographic algorithm; it is not even close to being production-ready.
 * It is only meant as an end-to-end test for OTBN during the bringup phase.
 *
 * The test contains constants and expected output, which can be independently
 * and conveniently verified using a Python script.
 *
 * <code>
 * # Optional: generate a new key
 * $ openssl ecparam -name prime256v1 -genkey -noout -out \
 *     otbn_ecdsa_p256_test_private_key.pem
 *
 * # Create all constants/variables
 * $ ./otbn_test_params.py ecc otbn_ecdsa_p256_test_private_key.pem
 * </code>
 */

OTBN_DECLARE_APP_SYMBOLS(p256_ecdsa);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, p256_ecdsa_sign);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, p256_ecdsa_verify);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, k);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, rnd);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, msg);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, r);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, s);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, x);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, y);
OTBN_DECLARE_PTR_SYMBOL(p256_ecdsa, d);

static const otbn_app_t kOtbnAppP256Ecdsa = OTBN_APP_T_INIT(p256_ecdsa);
static const otbn_ptr_t kOtbnAppP256EcdsaFuncSign =
    OTBN_PTR_T_INIT(p256_ecdsa, p256_ecdsa_sign);
static const otbn_ptr_t kOtbnAppP256EcdsaFuncVerify =
    OTBN_PTR_T_INIT(p256_ecdsa, p256_ecdsa_verify);
static const otbn_ptr_t kOtbnVarK = OTBN_PTR_T_INIT(p256_ecdsa, k);
static const otbn_ptr_t kOtbnVarRnd = OTBN_PTR_T_INIT(p256_ecdsa, rnd);
static const otbn_ptr_t kOtbnVarMsg = OTBN_PTR_T_INIT(p256_ecdsa, msg);
static const otbn_ptr_t kOtbnVarR = OTBN_PTR_T_INIT(p256_ecdsa, r);
static const otbn_ptr_t kOtbnVarS = OTBN_PTR_T_INIT(p256_ecdsa, s);
static const otbn_ptr_t kOtbnVarX = OTBN_PTR_T_INIT(p256_ecdsa, x);
static const otbn_ptr_t kOtbnVarY = OTBN_PTR_T_INIT(p256_ecdsa, y);
static const otbn_ptr_t kOtbnVarD = OTBN_PTR_T_INIT(p256_ecdsa, d);

const test_config_t kTestConfig;

/**
 * CHECK()s that the actual data matches the expected data.
 *
 * @param actual The actual data.
 * @param expected The expected data.
 * @param size_bytes The size of the actual/expected data.
 */
static void check_data(const char *msg, const uint8_t *actual,
                       const uint8_t *expected, size_t size_bytes) {
  for (int i = 0; i < size_bytes; ++i) {
    CHECK(actual[i] == expected[i],
          "%s: mismatch at byte %d: 0x%x (actual) != 0x%x (expected)", msg, i,
          actual[i], expected[i]);
  }
}

/**
 * Starts a profiling section.
 *
 * Call this function at the start of a section that should be profiled, and
 * call `profile_end()` at the end of it to display the results.
 *
 * @return The cycle counter when starting the profiling.
 */
static uint64_t profile_start(void) { return ibex_mcycle_read(); }

/**
 * Ends a profiling section.
 *
 * The time since `profile_start()` is printed as log message.
 *
 * @param t_start Start timestamp, as returned from profile_start().
 * @param msg Name of the operation (for logging purposes).
 */
static void profile_end(uint64_t t_start, const char *msg) {
  uint64_t t_end = ibex_mcycle_read();
  uint32_t cycles = t_end - t_start;
  uint32_t time_us = cycles / 100;
  LOG_INFO("%s took %u cycles or %u us @ 100 MHz.", msg, cycles, time_us);
}

/**
 * Signs a message with ECDSA using the P-256 curve.
 *
 * @param otbn_ctx            The OTBN context object.
 * @param msg                 The message to sign (32B).
 * @param secret_random_int_k The secret random integer (32B).
 * @param private_key_d       The private key (32B).
 * @param[out] signature_r    Signature component r (the x-coordinate of R).
 *                            Provide a pre-allocated 32B buffer.
 * @param[out] signature_s    Signature component s (the proof).
 *                            Provide a pre-allocated 32B buffer.
 */
static void p256_ecdsa_sign(otbn_t *otbn_ctx, const uint8_t *msg,
                            const uint8_t *secret_random_int_k,
                            const uint8_t *private_key_d, uint8_t *signature_r,
                            uint8_t *signature_s) {
  CHECK(otbn_ctx != NULL);

  // Write input arguments.
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, msg, kOtbnVarMsg) ==
        kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, secret_random_int_k,
                               kOtbnVarK) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, private_key_d,
                               kOtbnVarD) == kOtbnOk);

  // Call OTBN to perform operation, and wait for it to complete.
  CHECK(otbn_call_function(otbn_ctx, kOtbnAppP256EcdsaFuncSign) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);

  // Read back results.
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarR,
                                 signature_r) == kOtbnOk);
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarS,
                                 signature_s) == kOtbnOk);
}

/**
 * Verifies a message with ECDSA using the P-256 curve.
 *
 * @param otbn_ctx             The OTBN context object.
 * @param msg                  The message to verify (32B).
 * @param signature_s          The signature component s (the proof) (32B).
 * @param public_key_x         The public key x-coordinate (32B).
 * @param public_key_y         The public key y-coordinate (32B).
 * @param[out] signature_r_out Recovered point r' (== R'.x). Provide a
 *                             pre-allocated 32B buffer.
 */
static void p256_ecdsa_verify(otbn_t *otbn_ctx, const uint8_t *msg,
                              const uint8_t *signature_s,
                              const uint8_t *public_key_x,
                              const uint8_t *public_key_y,
                              uint8_t *signature_r_out) {
  CHECK(otbn_ctx != NULL);

  // Write input arguments.
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, msg, kOtbnVarMsg) ==
        kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, signature_s,
                               kOtbnVarS) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, public_key_x,
                               kOtbnVarX) == kOtbnOk);
  CHECK(otbn_copy_data_to_otbn(otbn_ctx, /*len_bytes=*/32, public_key_y,
                               kOtbnVarY) == kOtbnOk);

  // Call OTBN to perform operation, and wait for it to complete.
  CHECK(otbn_call_function(otbn_ctx, kOtbnAppP256EcdsaFuncVerify) == kOtbnOk);
  CHECK(otbn_busy_wait_for_done(otbn_ctx) == kOtbnOk);

  // Read back results.
  CHECK(otbn_copy_data_from_otbn(otbn_ctx, /*len_bytes=*/32, kOtbnVarRnd,
                                 signature_r_out) == kOtbnOk);
}

/**
 * Performs a ECDSA roundtrip test using the NIST P-256 curve.
 *
 * A roundtrip consists of three steps: Initialize OTBN, sign, and verify.
 */
static void test_ecdsa_p256_roundtrip(void) {
  // Message
  static const uint8_t kIn[32] = {"Hello OTBN."};

  // Public key x-coordinate (Q.x)
  static const uint8_t kPublicKeyQx[32] = {
      0x4e, 0xb2, 0x8b, 0x55, 0xeb, 0x88, 0x62, 0x24, 0xf2, 0xbf, 0x1b,
      0x9e, 0xd8, 0x4a, 0x09, 0xa7, 0x86, 0x67, 0x92, 0xcd, 0xca, 0x07,
      0x5d, 0x07, 0x82, 0xe7, 0x2d, 0xac, 0x31, 0x14, 0x79, 0x1f};

  // Public key y-coordinate (Q.y)
  static const uint8_t kPublicKeyQy[32] = {
      0x27, 0x9c, 0xe4, 0x23, 0x24, 0x10, 0xa2, 0xfa, 0xbd, 0x53, 0x73,
      0xf1, 0xa5, 0x08, 0xf0, 0x40, 0x9e, 0xc0, 0x55, 0x21, 0xa4, 0xf0,
      0x54, 0x59, 0x00, 0x3e, 0x5f, 0x15, 0x3c, 0xc6, 0x4b, 0x87};

  // Private key (d)
  static const uint8_t kPrivateKeyD[32] = {
      0xcd, 0xb4, 0x57, 0xaf, 0x1c, 0x9f, 0x4c, 0x74, 0x02, 0x0c, 0x7e,
      0x8b, 0xe9, 0x93, 0x3e, 0x28, 0x0c, 0xf0, 0x18, 0x0d, 0xf4, 0x6c,
      0x0b, 0xda, 0x7a, 0xbb, 0xe6, 0x8f, 0xb7, 0xa0, 0x45, 0x55};

  // Secret random integer (k)
  static const uint8_t kSecretRandomIntK[32] = {
      0x7d, 0x07, 0x40, 0x6b, 0x57, 0x4f, 0xc1, 0xfe, 0x0a, 0x56, 0x3e,
      0x81, 0xd4, 0x10, 0x75, 0x6a, 0x86, 0x8e, 0x1d, 0x07, 0x42, 0x25,
      0xc9, 0xeb, 0x89, 0xae, 0x7b, 0x02, 0x49, 0x87, 0x65, 0x4d};

  // Signature component r
  static const uint8_t kExpectedSignatureR[32] = {
      0xb2, 0x9c, 0x5e, 0xc1, 0xff, 0x9c, 0xa9, 0x70, 0xb8, 0xd7, 0x7d,
      0x90, 0xbb, 0x29, 0x8d, 0x5f, 0x8f, 0x96, 0x42, 0x66, 0x5f, 0xe8,
      0x49, 0x59, 0xf7, 0x43, 0xb8, 0x03, 0x5b, 0xf7, 0x89, 0x04};

  // Signature component s
  static const uint8_t kExpectedSignatureS[32] = {
      0xdd, 0x33, 0x60, 0x07, 0x1e, 0x60, 0x06, 0xa4, 0xe2, 0xfa, 0x41,
      0xf9, 0xf1, 0x69, 0xa5, 0x79, 0x38, 0x0c, 0xcd, 0x66, 0x88, 0xda,
      0x25, 0x2e, 0x23, 0x56, 0x81, 0x62, 0x28, 0xf8, 0x6b, 0xd1};

  // Initialize
  otbn_t otbn_ctx;
  dif_otbn_config_t otbn_config = {
      .base_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR),
  };
  uint64_t t_start_init = profile_start();
  CHECK(otbn_init(&otbn_ctx, otbn_config) == kOtbnOk);
  CHECK(otbn_load_app(&otbn_ctx, kOtbnAppP256Ecdsa) == kOtbnOk);
  profile_end(t_start_init, "Initialization");

  // Sign
  uint8_t signature_r[32] = {0};
  uint8_t signature_s[32] = {0};

  LOG_INFO("Signing");
  uint64_t t_start_sign = profile_start();
  p256_ecdsa_sign(&otbn_ctx, kIn, kSecretRandomIntK, kPrivateKeyD, signature_r,
                  signature_s);
  profile_end(t_start_sign, "Sign");
  check_data("signature_r", signature_r, kExpectedSignatureR, 32);
  check_data("signature_s", signature_s, kExpectedSignatureS, 32);

  // Verify
  uint8_t signature_r_out[32] = {0};

  LOG_INFO("Verifying");
  uint64_t t_start_verify = profile_start();
  p256_ecdsa_verify(&otbn_ctx, kIn, signature_s, kPublicKeyQx, kPublicKeyQy,
                    signature_r_out);

  // Include the r =? r' comparison in the profiling as this is something
  // either OTBN or the host CPU needs to do as part of the signature
  // verification.
  check_data("signature_r_out", signature_r_out, signature_r, 32);
  profile_end(t_start_verify, "Verify");
}

bool test_main() {
  test_ecdsa_p256_roundtrip();

  return true;
}
