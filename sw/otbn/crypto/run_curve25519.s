/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for 25519 ECDH (X25519) and ECDSA (ed25519) operations.
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
.equ MODE_X25519, 0x4B1
.equ MODE_X25519_KEYGEN, 0x5A9

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_KEYGEN
.globl MODE_SIGN_STAGE1
.globl MODE_SIGN_STAGE2
.globl MODE_VERIFY
.globl MODE_X25519
.globl MODE_X25519_KEYGEN

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

  addi  x3, x0, MODE_X25519
  beq   x2, x3, x25519

  addi  x3, x0, MODE_X25519_KEYGEN
  beq   x2, x3, x25519_keygen

  /* Invalid mode; fail. */
  unimp
  unimp

x25519:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Load private key into w8 */
  li x2, 8
  la x3, x25519_private_key
  bn.lid x2, 0(x3)

  /* Load public key into w9 */
  li x2, 9
  la x3, x25519_public_key
  bn.lid x2, 0(x3)

  /* Call x25519 basepoint multiplication */
  jal x1, X25519

  /* Store shared key from w22 */
  li x2, 22
  la x3, x25519_shared_key
  bn.sid x2, 0(x3)

  ecall

x25519_keygen:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Load private key into w8 */
  li x2, 8
  la x3, x25519_private_key
  bn.lid x2, 0(x3)

  /* Set public key to 9 */
  bn.addi w9, w31, 9

  /* Call x25519 */
  jal x1, X25519

  /* Store public key from w22 */
  li x2, 22
  la x3, x25519_public_key
  bn.sid x2, 0(x3)

  ecall
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
   If verification is successful, this will be SUCCESS = 0x739.
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

/* Precomputed arithmetic shares of the clamped integer s (256 bits embedded in
   384 bits). See RFC 8032, section 5.1.6, step 1 or the docstring of
   ed25519_sign. Input for sign. */
.balign 32
.globl ed25519_s0
ed25519_s0:
  .zero 64

.balign 32
.globl ed25519_s1
ed25519_s1:
  .zero 64

/* Precomputed arithmetic shares of r (512 bits embedded in 640 bits). See
   RFC 8032, section 5.1.6, step 2 or the docstring of ed25519_sign.
   Input for sign. */
.balign 32
.globl ed25519_r0
ed25519_r0:
  .zero 96

.balign 32
.globl ed25519_r1
ed25519_r1:
  .zero 96

/* X25519 public key */
.balign 32
.globl x25519_public_key
x25519_public_key:
  .zero 32

/* Shared key (256 bits). Output for ecdh. */
.balign 32
.globl x25519_shared_key
x25519_shared_key:
  .zero 32

/* X25519 Private Key (256 bits). Input for ecdh and keygen. */
.balign 32
.globl x25519_private_key
x25519_private_key:
  .zero 32
