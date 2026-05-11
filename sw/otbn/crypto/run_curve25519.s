/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for 25519 ECDH (X25519) and EdDSA (ed25519) operations.
 *
 * This binary has the following modes of operation:
 * 1. MODE_SIGN_PART1: generate a new keypair
 * 2. MODE_SIGN_PART2: generate an EdDSA signature using caller-provided secret key
 */

/**
 * Mode magic values, generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 8 -n 11 \
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
.equ MODE_KEYGEN, 0x1F8
.equ MODE_SIGN_STAGE1, 0x669
.equ MODE_SIGN_STAGE2, 0x23E
.equ MODE_VERIFY, 0x54E
.equ MODE_X25519, 0x695
.equ MODE_X25519_KEYGEN, 0x7A2
.equ MODE_X25519_SIDELOAD, 0xE7
.equ MODE_X25519_KEYGEN_SIDELOAD, 0x353

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_KEYGEN
.globl MODE_SIGN_STAGE1
.globl MODE_SIGN_STAGE2
.globl MODE_VERIFY
.globl MODE_X25519
.globl MODE_X25519_KEYGEN
.globl MODE_X25519_SIDELOAD
.globl MODE_X25519_KEYGEN_SIDELOAD

.section .text.start
.globl start
start:
  /* Read the mode and tail-call the requested operation. */
  la    x2, mode
  lw    x2, 0(x2)

  addi  x3, x0, MODE_KEYGEN
  beq   x2, x3, ed25519_keygen

  addi  x3, x0, MODE_SIGN_STAGE1
  beq   x2, x3, ed25519_sign_compute_r

  addi  x3, x0, MODE_SIGN_STAGE2
  beq   x2, x3, ed25519_sign_compute_s

  addi  x3, x0, MODE_VERIFY
  beq   x2, x3, ed25519_verify

  addi  x3, x0, MODE_X25519
  beq   x2, x3, x25519

  addi  x3, x0, MODE_X25519_KEYGEN
  beq   x2, x3, x25519_keygen

  addi  x3, x0, MODE_X25519_SIDELOAD
  beq   x2, x3, x25519_sideload

  addi  x3, x0, MODE_X25519_KEYGEN_SIDELOAD
  beq   x2, x3, x25519_keygen_sideload

  /* Invalid mode; fail. */
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
ed25519_keygen:
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
ed25519_sign_compute_r:
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
ed25519_sign_compute_s:
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

x25519:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Load private key arithmetic shares into w8 and w7 */
  li       x2, 8
  la       x3, ed25519_s0
  bn.lid   x2, 0(x3)

  li       x2, 7
  la       x3, ed25519_s1
  bn.lid   x2, 0(x3)

  /* A_lo = w8, A_hi = 0 */
  bn.add   w11, w8, w31
  bn.xor   w12, w31, w31

  /* r_lo = w7, r_hi = 0 */
  bn.add   w18, w7, w31
  bn.xor   w19, w31, w31

  /* Convert arithmetic shares to boolean shares */
  jal      x1, arithmetic_to_boolean

  /* x'_lo (w20) -> w8 (Share 0), r_lo (w18) -> w7 (Share 1) */
  bn.add   w8, w20, w31
  bn.add   w7, w18, w31

  /* Clamp the boolean shares */
  jal      x1, x25519_clamp_shares

  /* s0_lo = w8, s0_hi = 0 */
  bn.add   w20, w8, w31
  bn.xor   w21, w31, w31

  /* s1_lo = w7, s1_hi = 0 */
  bn.add   w10, w7, w31
  bn.xor   w11, w31, w31

  /* Convert boolean shares back to arithmetic ones */
  jal      x1, boolean_to_arithmetic

  /* w4 = 254-bit random mask B */
  bn.wsrr  w4, URND
  bn.rshi  w4, w31, w4 >> 2

  /* w5 = w10 + w4 (x1 + B) */
  bn.add   w5, w10, w4
  bn.xor   w31, w31, w31 /* clear flags */

  /* w2 = w20 + w5 (x0 + x1 + B) */
  bn.add   w2, w20, w5

  /* Clear flags before jump */
  bn.sub   w31, w31, w31, FG0

  /* Load public key into w9 */
  li       x2, 9
  la       x3, x25519_public_key
  bn.lid   x2, 0(x3)

  /* Call Edwards-mapped X25519 */
  jal      x1, X25519

  /* Store result status (SUCCESS or FAILURE) from x20. */
  la       x3, x25519_ok
  sw       x20, 0(x3)

  /* Store shared key from w22 */
  li       x2, 22
  la       x3, x25519_shared_key
  bn.sid   x2, 0(x3)

  ecall

x25519_keygen:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Load private key arithmetic shares into w8 and w7 */
  li       x2, 8
  la       x3, ed25519_s0
  bn.lid   x2, 0(x3)

  li       x2, 7
  la       x3, ed25519_s1
  bn.lid   x2, 0(x3)

  /* A_lo = w8, A_hi = 0 */
  bn.add w11, w8, w31
  bn.xor w12, w31, w31

  /* r_lo = w7, r_hi = 0 */
  bn.add w18, w7, w31
  bn.xor w19, w31, w31

  /* Convert arithmetic shares to boolean shares */
  jal  x1, arithmetic_to_boolean

  /* x'_lo (w20) -> w8 (Share 0), r_lo (w18) -> w7 (Share 1) */
  bn.add   w8, w20, w31
  bn.add   w7, w18, w31

  /* Clamp the boolean shares */
  jal      x1, x25519_clamp_shares

  /* s0_lo = w8, s0_hi = 0 */
  bn.add w20, w8, w31
  bn.xor w21, w31, w31

  /* s1_lo = w7, s1_hi = 0 */
  bn.add w10, w7, w31
  bn.xor w11, w31, w31

  /* Convert boolean shares back to arithmetic ones */
  jal x1, boolean_to_arithmetic

  /* w4 = 254-bit random mask B */
  bn.wsrr w4, URND
  bn.rshi w4, w31, w4 >> 2

  /* w5 = w10 + w4 (x1 + B) */
  bn.add w5, w10, w4
  bn.xor w31, w31, w31 /* clear flags */

  /* w2 = w20 + w5 (x0 + x1 + B) */
  bn.add w2, w20, w5

  /* Clear flags before jump */
  bn.sub w31, w31, w31, FG0

  /* Set Curve25519 basepoint */
  bn.addi  w9, w31, 9

  jal      x1, X25519

  /* Store public key from w22 */
  li       x2, 22
  la       x3, x25519_public_key
  bn.sid   x2, 0(x3)

  ecall

x25519_sideload:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Read private key shares */
  bn.wsrr w8, KEY_S0_L
  bn.wsrr w7, KEY_S1_L

  /* Clamp the Boolean shares */
  jal x1, x25519_clamp_shares

  /* s0_lo = w8, s0_hi = 0 */
  bn.add w20, w8, w31
  bn.xor w21, w31, w31

  /* s1_lo = w7, s1_hi = 0 */
  bn.add w10, w7, w31
  bn.xor w11, w31, w31

  /* Convert boolean shares back to arithmetic ones */
  jal x1, boolean_to_arithmetic

  /* w4 = 254-bit random mask B */
  bn.wsrr w4, URND
  bn.rshi w4, w31, w4 >> 2

  /* w5 = w10 + w4 (x1 + B) */
  bn.add w5, w10, w4
  bn.xor w31, w31, w31 /* clear flags */

  /* w2 = w20 + w5 (x0 + x1 + B) */
  bn.add w2, w20, w5

  /* Clear flags before jump */
  bn.sub w31, w31, w31, FG0

  /* Load public key into w9 */
  li x2, 9
  la x3, x25519_public_key
  bn.lid x2, 0(x3)

  jal x1, X25519

  /* Store result status (SUCCESS or FAILURE) from x20. */
  la       x3, x25519_ok
  sw       x20, 0(x3)

  /* Store shared key from w22 */
  li x2, 22
  la x3, x25519_shared_key
  bn.sid x2, 0(x3)

  ecall

x25519_keygen_sideload:
  /* Zeroize w31 */
  bn.xor   w31, w31, w31

  /* Read private key shares */
  bn.wsrr w7, KEY_S0_L
  bn.wsrr w8, KEY_S1_L

  /* Clamp the Boolean shares */
  jal x1, x25519_clamp_shares

  /* s0_lo = w8, s0_hi = 0 */
  bn.add w20, w8, w31
  bn.xor w21, w31, w31

  /* s1_lo = w7, s1_hi = 0 */
  bn.add w10, w7, w31
  bn.xor w11, w31, w31

  /* Convert boolean shares back to arithmetic ones */
  jal x1, boolean_to_arithmetic

  /* w4 = 254-bit random mask B */
  bn.wsrr w4, URND
  bn.rshi w4, w31, w4 >> 2

  /* w5 = w10 + w4 (x1 + B) */
  bn.add w5, w10, w4
  bn.xor w31, w31, w31 /* clear flags */

  /* w2 = w20 + w5 (x0 + x1 + B) */
  bn.add w2, w20, w5

  /* Clear flags before jump */
  bn.sub w31, w31, w31, FG0

  /* Set Curve25519 basepoint */
  bn.addi w9, w31, 9

  jal x1, X25519

  /* Store public key from w22 into DMEM */
  li x2, 22
  la x3, x25519_public_key
  bn.sid x2, 0(x3)

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

/* X25519 result status (SUCCESS=0x739 or FAILURE=0x1d4). Output for x25519. */
.balign 4
.globl x25519_ok
x25519_ok:
  .zero 4

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
