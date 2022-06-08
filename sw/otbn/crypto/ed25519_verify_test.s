/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone unit tests for Ed25519 signature verification.
 *
 * Tests included in this file are intended for quick sanity-checks of
 * subroutines; they will not cover all edge cases.
 *
 * This test will exit with the number of failures written to the w0 register;
 * w0=0 means all tests succeeded.
 */

.section .text.start

main:
  /* Prepare all-zero register. */
  bn.xor  w31, w31, w31

  /* Initialize failure counter to 0. */
  bn.mov  w0, w31

  /* Run tests. */
  jal     x1, run_rfc_test1
  jal     x1, run_test_negative

  ecall

/**
 * Check test 1 from RFC 8032, section 7.1.
 *
 * Attempt to verify the signature from the test vector; it should pass.
 *
 * @param[in]  w0: test failure counter
 * @param[in]  w31: all-zero
 * @param[in]  dmem[ed25519_hash_k]: precomputed hash k
 * @param[in]  dmem[ed25519_sig_R]: R, first half of signature for test
 * @param[in]  dmem[ed25519_sig_S]: S, second half of signature for test
 * @param[in]  dmem[ed25519_public_key]: A, public key for test
 * @param[out] w0: updatedtest failure counter
 *
 * clobbered registers: x2 to x4, x20 to x23, w0, w2 to w30
 * clobbered flag groups: FG0
 */
run_rfc_test1:
  /* Attempt to verify the signature.
       dmem[ed25519_verify_result] <= SUCCESS or FAILURE */
  jal      x1, ed25519_verify_var

  /* Load SUCCESS magic value. */
  li       x21, 0xf77fe650

  /* Load the verification result.
       x3 <= dmem[ed25519_verify_result] */
  la       x2, ed25519_verify_result
  lw       x3, 0(x2)

  /* Increment failure counter if the test failed.
     w0 <= w0 if x3 == SUCCESS, else w0 + 1 */
  beq      x3, x21, test1_success
  bn.addi  w0, w0, 1
  test1_success:

  ret

/**
 * Check that verifying an invalid signature fails.
 *
 * Uses the public key and k values from RFC 8032, section 7.1, test 1.
 *
 * @param[in]  w0: test failure counter
 * @param[in]  w31: all-zero
 * @param[in]  dmem[ed25519_hash_k]: precomputed hash k
 * @param[in]  dmem[ed25519_sig_R]: R, first half of signature for test
 * @param[in]  dmem[ed25519_sig_S]: S, second half of signature for test
 * @param[in]  dmem[ed25519_public_key]: A, public key for test
 * @param[out] w0: updatedtest failure counter
 *
 * clobbered registers: x2 to x4, x20 to x23, w0, w2 to w30
 * clobbered flag groups: FG0
 */
run_test_negative:
  /* Reverse R (signature point) and A (public key point). This way, both are
     still valid points, so point decoding succeeds, but the signature is not
     valid. */

  /* w2 <= dmem[ed25519_sig_R] */
  li       x3, 2
  la       x2, ed25519_sig_R
  bn.lid   x3, 0(x2)

  /* w3 <= dmem[ed25519_public_key] */
  li       x3, 3
  la       x2, ed25519_public_key
  bn.lid   x3, 0(x2)

  /* dmem[ed25519_sig_R] <= w3 */
  li       x3, 3
  la       x2, ed25519_sig_R
  bn.sid   x3, 0(x2)

  /* dmem[ed25519_public_key] <= w2 */
  li       x3, 2
  la       x2, ed25519_public_key
  bn.sid   x3, 0(x2)

  /* Attempt to verify the signature.
       dmem[ed25519_verify_result] <= SUCCESS or FAILURE */
  jal      x1, ed25519_verify_var

  /* Load FAILURE magic value. */
  li       x22, 0xeda2bfaf

  /* Load the verification result.
       x3 <= dmem[ed25519_verify_result] */
  la       x2, ed25519_verify_result
  lw       x3, 0(x2)

  /* Increment failure counter if the signature passed.
     w0 <= w0 if x3 == FAILURE, else w0 + 1 */
  beq      x3, x22, test_negative_success
  bn.addi  w0, w0, 1
  test_negative_success:

  ret

.data

/**
 * Data from RFC 8032, Section 7.1, Test 1. From the RFC:
 *   -----TEST 1
 *
 *   ALGORITHM:
 *   Ed25519
 *
 *   SECRET KEY:
 *   9d61b19deffd5a60ba844af492ec2cc4
 *   4449c5697b326919703bac031cae7f60
 *
 *   PUBLIC KEY:
 *   d75a980182b10ab7d54bfed3c964073a
 *   0ee172f3daa62325af021a68f707511a
 *
 *   MESSAGE (length 0 bytes):
 *
 *   SIGNATURE:
 *   e5564300c360ac729086e2cc806e828a
 *   84877f1eb8e5d974d873e06522490155
 *   5fb8821590a33bacc61e39701cf9b46b
 *   d25bf5f0595bbe24655141438e7a100b
 *
 * The value k = SHA2-512(dom2(F, C) || R || A || PH(M)) is precomputed. In
 * this case, dom2(F,C) is the empty string (because we're using Ed25519, not
 * Ed25519ph or Ed25519ctx: see RFC 8032, section 5.1). R is the first 32 bytes
 * of the signature, and A is the public key. PH is the identity function for
 * plain Ed25519. So that means, in this case, k = SHA2-512(R || A). Python
 * precomputation transcript for reference (the SHA-512 output is big-endian,
 * so it's reversed in the final data):
 *
 * >>> R = bytearray.fromhex('e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155')
 * >>> A = bytearray.fromhex('d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a')
 * >>> from Crypto.Hash import SHA512
 * >>> SHA512.new(R + A).hexdigest()
 * '2771062b6b536fe7ffbdda0320c3827b035df10d284df3f08222f04dbca7a4c20ef15bdc988a22c7207411377c33f2ac09b1e86a046234283768ee7ba03c0e9f'
 */
.globl ed25519_hash_k
.balign 32
ed25519_hash_k:
  .word 0x2b067127
  .word 0xe76f536b
  .word 0x03dabdff
  .word 0x7b82c320
  .word 0x0df15d03
  .word 0xf0f34d28
  .word 0x4df02282
  .word 0xc2a4a7bc
  .word 0xdc5bf10e
  .word 0xc7228a98
  .word 0x37117420
  .word 0xacf2337c
  .word 0x6ae8b109
  .word 0x28346204
  .word 0x7bee6837
  .word 0x9f0e3ca0

.globl ed25519_sig_R
.balign 32
ed25519_sig_R:
  .word 0x004356e5
  .word 0x72ac60c3
  .word 0xcce28690
  .word 0x8a826e80
  .word 0x1e7f8784
  .word 0x74d9e5b8
  .word 0x65e073d8
  .word 0x55014922

.globl ed25519_sig_S
.balign 32
ed25519_sig_S:
  .word 0x1582b85f
  .word 0xac3ba390
  .word 0x70391ec6
  .word 0x6bb4f91c
  .word 0xf0f55bd2
  .word 0x24be5b59
  .word 0x43415165
  .word 0x0b107a8e

.globl ed25519_public_key
.balign 32
ed25519_public_key:
  .word 0x01985ad7
  .word 0xb70ab182
  .word 0xd3fe4bd5
  .word 0x3a0764c9
  .word 0xf372e10e
  .word 0x2523a6da
  .word 0x681a02af
  .word 0x1a5107f7
