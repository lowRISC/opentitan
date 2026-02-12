/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-256 ECDH and ECDSA operations.
 *
 * This binary has the following modes of operation:
 * 1. MODE_SIGN_PART1: generate a new keypair
 * 2. MODE_SIGN_PART2: generate an ECDSA signature using caller-provided secret key
 */

/**
 * Mode magic values, generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 3 -n 11 \
 *     --avoid-zero -s 380925547
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_KEYGEN, 0x6CE
.equ MODE_SIGN_STAGE1, 0x77D
.equ MODE_SIGN_STAGE2, 0x397
.equ MODE_VERIFY, 0x5F2

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_KEYGEN
.globl MODE_SIGN_STAGE1
.globl MODE_SIGN_STAGE2
.globl MODE_VERIFY

.section .text.start
.globl start
start:
  /* Read the mode and tail-call the requested operation. */
  la    x2, mode
  lw    x2, 0(x2)

  addi  x3, x0, MODE_KEYGEN
  beq   x2, x3, ecdsa_keygen

  addi  x3, x0, MODE_SIGN_STAGE1
  beq   x2, x3, ecdsa_sign_compute_r

  addi  x3, x0, MODE_SIGN_STAGE2
  beq   x2, x3, ecdsa_sign_compute_s

  addi  x3, x0, MODE_VERIFY
  beq   x2, x3, ed25519_verify

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp

/**
 * Ed25519 key generation operation.
 * Generate the encoded public key A.
 *
 * Returns A_ (encoded public key point).
 *
 * @param[in]  dmem[ed25519_hash_h_low]: lower half of precomputed hash h, 256 bits
 * @param[out] dmem[ed25519_public_key]: encoded public key A_, 256 bits
 *
 * clobbered registers: x2 to x3, w2 to w31
 * clobbered flag groups: FG0
 */
ecdsa_keygen:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Set up for scalar arithmetic.
       [w15:w14] <= mu
       MOD <= L */
  jal      x1, sc_init

  /* Generate the public key. */
  jal      x1, ed25519_gen_public_key

  ecall

/**
 * Ed25519 signature generation operation (first stage).
 * Generate the encoded signature point R and public key A.
 *
 * Returns R_ (encoded signature point) and A_ (encoded public key point).
 *
 * @param[in]  dmem[ed25519_hash_r]: precomputed hash r, 512 bits
 * @param[in]  dmem[ed25519_hash_h_low]: lower half of precomputed hash h, 256 bits
 * @param[out] dmem[ed25519_sig_R]: encoded signature point R_, 256 bits
 * @param[out] dmem[ed25519_public_key]: encoded public key A_, 256 bits
 *
 * clobbered registers: x2 to x3, w2 to w31
 * clobbered flag groups: FG0
 */
ecdsa_sign_compute_r:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Generate the signature. */
  jal      x1, ed25519_sign_stage1

  ecall

/**
 * Ed25519 signature generation operation (second stage).
 * Generate the signature scalar S.
 *
 * Returns S (a scalar modulo L), the second half of the signature.
 *
 * @param[in]  dmem[ed25519_hash_k]: precomputed hash k, 512 bits
 * @param[in]  dmem[ed25519_hash_r]: precomputed hash r, 512 bits
 * @param[in]  dmem[ed25519_hash_h_low]: lower half of precomputed hash h, 256 bits
 * @param[out] dmem[ed25519_sig_S]: signature scalar S, 256 bits
 *
 * clobbered registers: x2 to x4, x20 to x23, w2 to w31
 * clobbered flag groups: FG0
 */
ecdsa_sign_compute_s:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Generate the signature. */
  jal      x1, ed25519_sign_stage2

  ecall

/**
 * Ed25519 signature verification operation.
 *
 * Returns SUCCESS or FAILURE.
 *
 * @param[in]  dmem[ed25519_hash_k]: precomputed hash k, 512 bits
 * @param[in]  dmem[ed25519_sig_R]: encoded signature point R_, 256 bits
 * @param[in]  dmem[ed25519_sig_S]: signature scalar S, 256 bits
 * @param[in]  dmem[ed25519_public_key]: encoded public key A_, 512 bits
 * @param[out] dmem[ed25519_verify_result]: SUCCESS or FAILURE
 *
 * clobbered registers: x2 to x4, x20 to x23, w2 to w31
 * clobbered flag groups: FG0
 */
ed25519_verify:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Generate the signature. */
  jal      x1, ed25519_verify_var

  ecall

.bss

/* Operation mode. */
.globl mode
.balign 4
mode:
  .zero 4

/* Verification result code (32 bits). Output for verify.
   If verification is successful, this will be SUCCESS = 0xf77fe650.
   Otherwise, this will be FAILURE = 0xeda2bfaf. */
.balign 32
.globl ed25519_verify_result
ed25519_verify_result:
  .zero 4

/* Signature point R (256 bits). Input for verify and output for sign. */
.balign 32
.globl ed25519_sig_R
ed25519_sig_R:
  .zero 32

/* Signature scalar S (253 bits). Input for verify and output for sign. */
.balign 32
.globl ed25519_sig_S
ed25519_sig_S:
  .zero 32

/* Encoded public key A_ (256 bits). Input for verify. */
.balign 32
.globl ed25519_public_key
ed25519_public_key:
  .zero 32

/* Precomputed hash k (512 bits). Input for verify and sign. */
.balign 32
.globl ed25519_hash_k
ed25519_hash_k:
  .zero 64

/* Lower half of precomputed hash h (256 bits). See RFC 8032, section
   5.1.6, step 1 or the docstring of ed25519_sign. Input for sign. */
.balign 32
.globl ed25519_hash_h_low
ed25519_hash_h_low:
  .zero 32

/* Precomputed hash r (512 bits). See RFC 8032, section 5.1.6, step 2 or the
   docstring of ed25519_sign. Input for sign. */
.balign 32
.globl ed25519_hash_r
ed25519_hash_r:
  .zero 64
