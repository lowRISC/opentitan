/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Elliptic-curve Diffie-Hellman (ECDH) on curve P-384.
 *
 * This binary has the following modes of operation:
 * 1. MODE_KEYGEN_RANDOM: generate a random keypair
 * 2. MODE_SHARED_KEYGEN: compute shared key - !!! Attention !!! - before
 *                        shared key computation p384_curve_point_valid
 *                        binary has to be executed to check if the provided
 *                        public key is valid.
 */

 /**
 * Mode magic values generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 4 -n 11 \
 *    --avoid-zero -s 3660400884
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_SHARED_KEY, 0x5ec
.equ MODE_KEYPAIR_RANDOM, 0x3f1

.section .text.start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la        x2, mode
  lw        x2, 0(x2)

  addi      x3, x0, MODE_KEYPAIR_RANDOM
  beq       x2, x3, keypair_random

  addi      x3, x0, MODE_SHARED_KEY
  beq       x2, x3, shared_key

  /* Unsupported mode; fail. */
  unimp
  unimp
  unimp

/**
 * Generate a fresh random keypair.
 *
 * Returns secret key d in 448-bit shares d0, d1.
 *
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * This routine runs in constant time (except potentially waiting for entropy
 * from RND).
 *
 * @param[in]        w31: all-zero
 * @param[out]  dmem[d0]: 1st private key share d0
 * @param[out]  dmem[d1]: 2nd private key share d1
 * @param[out]   dmem[x]: Public key x-coordinate
 * @param[out]   dmem[y]: Public key y-coordinate
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
keypair_random:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, p384_generate_random_key

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal       x1, p384_base_mult

  ecall

/**
 * Generate a shared key from a secret and public key.
 *
 * Returns the shared key, which is the affine x-coordinate of (d*Q). The
 * shared key is expressed in boolean shares x0, x1 such that the key is (x0 ^
 * x1).
 *
 * This routine runs in constant time.
 *
 * !!! Attention !!! - before shared key computation p384_curve_point_valid
 * binary has to be executed to check if the provided public key is valid.
 *
 * @param[in]        w31: all-zero
 * @param[in]   dmem[k0]: 1st private key share d0/k0
 * @param[in]   dmem[k1]: 2nd private key share d1/k0
 * @param[in]    dmem[x]: x-coordinate of public key
 * @param[in]    dmem[y]: y-coordinate of public key
 * @param[out]   dmem[x]: x0, first share of shared key.
 * @param[out]   dmem[y]: x1, second share of shared key.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
shared_key:
  /* Generate arithmetically masked shared key d*Q.
     dmem[x] <= (d*Q).x - m mod p
     dmem[y] <= m */
  jal       x1, p384_scalar_mult

  /* Arithmetic-to-boolean conversion*/

  /* load result to WDRs for a2b conversion.
     [w12,w11] <= dmem[x] = x_m
     [w19,w18] <= dmem[y] = m */
  li        x2, 11
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  li        x2, 18
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  jal       x1, p384_arithmetic_to_boolean_mod

  /* Store arithmetically masked key to DMEM
     dmem[x] <= [w21,w20] = x_m' */
  li        x2, 20
  la        x3, x
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  ecall

.data

/* Operational mode. */
.globl mode
.balign 4
mode:
  .zero 4

/* Public key x-coordinate. */
.globl x
.balign 32
x:
  .zero 64

/* Public key y-coordinate. */
.globl y
.balign 32
y:
  .zero 64

/* Secret key (d) in two shares: d = (d0 + d1) mod n.

   Note: This is also labeled k0, k1 because the `p384_scalar_mult` algorithm
   is also used for ECDSA signing and reads from those labels; in the case of
   ECDH, the scalar in `p384_scalar_mult` is always the private key (d). */

.globl d0
.globl k0
.balign 32
d0:
k0:
  .zero 64

.globl d1
.globl k1
.balign 32
d1:
k1:
  .zero 64
