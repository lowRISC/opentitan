/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Elliptic-curve Diffie-Hellman (ECDH) on curve P-256.
 *
 * This binary has the following modes of operation:
 * 1. MODE_KEYGEN_RANDOM: generate a random keypair
 * 2. MODE_SHARED_KEYGEN: compute shared key
 * 3. MODE_KEYGEN_FROM_SEED: generate keypair from a sideloaded seed
 * 4. MODE_SHARED_KEYGEN_FROM_SEED: compute shared key using sideloaded seed
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
.equ MODE_KEYPAIR_RANDOM, 0x3f1
.equ MODE_SHARED_KEY, 0x5ec
.equ MODE_KEYPAIR_FROM_SEED, 0x29f
.equ MODE_SHARED_KEY_FROM_SEED, 0x74b

/**
 * Hardened boolean values.
 *
 * Should match the values in `hardened_asm.h`.
 */
.equ HARDENED_BOOL_TRUE, 0x739
.equ HARDENED_BOOL_FALSE, 0x1d4

.section .text.start
start:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la      x2, mode
  lw      x2, 0(x2)

  addi    x3, x0, MODE_KEYPAIR_RANDOM
  beq     x2, x3, keypair_random

  addi    x3, x0, MODE_SHARED_KEY
  beq     x2, x3, shared_key

  addi    x3, x0, MODE_KEYPAIR_FROM_SEED
  beq     x2, x3, keypair_from_seed

  addi    x3, x0, MODE_SHARED_KEY_FROM_SEED
  beq     x2, x3, shared_key_from_seed

  /* Unsupported mode; fail. */
  unimp
  unimp
  unimp

/**
 * Generate a fresh random keypair.
 *
 * Returns secret key d in 320b shares d0, d1.
 *
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * This routine runs in constant time (except potentially waiting for entropy
 * from RND).
 *
 * @param[in]       w31: all-zero
 * @param[out] dmem[d0]: First share of secret key.
 * @param[out] dmem[d1]: Second share of secret key.
 * @param[out]  dmem[x]: Public key x-coordinate.
 * @param[out]  dmem[y]: Public key y-coordinate.
 *
 * clobbered registers: x2, x3, x16, x17, x21, x22, w0 to w26
 * clobbered flag groups: FG0
 */
keypair_random:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal   x1, p256_generate_random_key

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal      x1, p256_base_mult

  ecall

/**
 * Generate a shared key from a secret and public key.
 *
 * Returns the shared key, which is the affine x-coordinate of (d*Q). The
 * shared key is expressed in boolean shares x0, x1 such that the key is (x0 ^
 * x1).
 *
 * If `ok` is false, the public key is invalid and the shared key is
 * meaningless. The value will be either HARDENED_BOOL_TRUE or
 * HARDENED_BOOL_FALSE.
 *
 * This routine runs in constant time.
 *
 * @param[in]       w31: all-zero
 * @param[in]  dmem[k0]: First share of secret key.
 * @param[in]  dmem[k1]: Second share of secret key.
 * @param[in]   dmem[x]: Public key (Q) x-coordinate.
 * @param[in]   dmem[y]: Public key (Q) y-coordinate.
 * @param[out] dmem[ok]: Whether the public key is valid.
 * @param[out]  dmem[x]: x0, first share of shared key.
 * @param[out]  dmem[y]: x1, second share of shared key.
 */
shared_key:
  /* Validate the public key (ends the program on failure). */
  jal      x1, p256_check_public_key

  /* If we got here the basic validity checks passed, so set `ok` to true. */
  la       x2, ok
  addi     x3, x0, HARDENED_BOOL_TRUE
  sw       x3, 0(x2)

  /* Generate boolean-masked shared key (d*Q).x.
       dmem[x] <= x0
       dmem[y] <= x1 */
  jal      x1, p256_shared_key

  ecall

/**
 * Generate a keypair from a keymgr-derived seed.
 *
 * Returns secret key d in 320b shares d0, d1.
 *
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * This routine runs in constant time.
 *
 * @param[in]       w31: all-zero
 * @param[out] dmem[d0]: First share of secret key.
 * @param[out] dmem[d1]: Second share of secret key.
 * @param[out]  dmem[x]: Public key x-coordinate.
 * @param[out]  dmem[y]: Public key y-coordinate.
 */
keypair_from_seed:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal   x1, secret_key_from_seed

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal      x1, p256_base_mult

  ecall

/**
 * Generate a shared key from a keymgr-derived seed.
 *
 * Returns the shared key, which is the affine x-coordinate of (d*Q). The
 * shared key is expressed in boolean shares x0, x1 such that the key is (x0 ^
 * x1).
 *
 * If `ok` is false, the public key is invalid and the shared key is
 * meaningless. The value will be either HARDENED_BOOL_TRUE or
 * HARDENED_BOOL_FALSE.
 *
 * This routine runs in constant time.
 *
 * @param[in]       w31: all-zero
 * @param[in]   dmem[x]: Public key (Q) x-coordinate.
 * @param[in]   dmem[y]: Public key (Q) y-coordinate.
 * @param[out] dmem[ok]: Whether the public key is valid.
 * @param[out]  dmem[x]: x0, first share of shared key.
 * @param[out]  dmem[y]: x1, second share of shared key.
 */
shared_key_from_seed:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal   x1, secret_key_from_seed

  /* Tail-call shared-key generation. */
  jal      x0, shared_key

/**
 * Generate a secret key from a keymgr-derived seed.
 *
 * Returns secret key d in 320b shares d0, d1 such that:
 *   (d0 + d1) mod n = (seed0 ^ seed1) mod n
 * ...where seed0 and seed1 are the 320-bit keymgr-provided seed values stored
 * in KEY_S0_{L,H} and KEY_S1_{L,H} WSRs. Note that the keymgr actually
 * provides 384 bits, but these higher bits are ignored.
 *
 * This routine runs in constant time.
 *
 * @param[in]       w31: all-zero
 * @param[out] dmem[d0]: First share of secret key.
 * @param[out] dmem[d0]: Second share of secret key.
 *
 * clobbered registers: x2, x3, w1 to w4, w20 to w29
 * clobbered flag groups: FG0
 */
secret_key_from_seed:
  /* Load keymgr seeds from WSRs.
       w20,w21 <= seed0
       w10,w11 <= seed1 */
  bn.wsrr  w20, KEY_S0_L
  bn.wsrr  w21, KEY_S0_H
  bn.wsrr  w10, KEY_S1_L
  bn.wsrr  w11, KEY_S1_H

  /* Generate secret key shares.
       w20, w21 <= d0
       w10, w11 <= d1 */
  jal      x1, p256_key_from_seed

  /* Store secret key shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  li       x2, 20
  la       x3, d0
  bn.sid   x2++, 0(x3)
  bn.sid   x2++, 32(x3)
  li       x2, 10
  la       x3, d1
  bn.sid   x2++, 0(x3)
  bn.sid   x2, 32(x3)

  ret

.bss

/* Operational mode. */
.globl mode
.balign 4
mode:
  .zero 4

/* Success code for basic validity checks on the public key. */
.globl ok
.balign 4
ok:
  .zero 4

/* Public key (Q) x-coordinate. */
.globl x
.balign 32
x:
  .zero 32

/* Public key y-coordinate. */
.globl y
.balign 32
y:
  .zero 32

/* Secret key (d) in two shares: d = (d0 + d1) mod n. */
.globl d0
.balign 32
d0:
k0:
  .zero 64

.globl d1
.balign 32
d1:
k1:
  .zero 64
