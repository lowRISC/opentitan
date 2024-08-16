/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-384 ECDSA key generation operations.
 *
 * This binary generates a new keypair.
 *
 * This binary has the following modes of operation:
 * 1. MODE_KEYGEN_RANDOM: generate a random keypair
 * 2. MODE_KEYGEN_FROM_SEED: generate a keypair from a sideloaded seed
 */

.equ MODE_KEYGEN_RANDOM, 0x3d4
.equ MODE_KEYGEN_FROM_SEED, 0x5e8

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_KEYGEN_RANDOM
.globl MODE_KEYGEN_FROM_SEED

.section .text.start
.globl start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la        x2, mode
  lw        x2, 0(x2)

  addi      x3, x0, MODE_KEYGEN_RANDOM
  beq       x2, x3, keypair_random

  addi      x3, x0, MODE_KEYGEN_FROM_SEED
  beq       x2, x3, keypair_from_seed

  /* Unsupported mode; fail. */
  unimp
  unimp
  unimp

/**
 * Generate a fresh random keypair.
 *
 * Returns secret key d in 448-bit shares d0, d1.
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * @param[in]       w31: all-zero
 * @param[out] dmem[d0]: 1st private key share d0
 * @param[out] dmem[d1]: 2nd private key share d1
 * @param[out]  dmem[x]: Public key x-coordinate
 * @param[out]  dmem[y]: Public key y-coordinate

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
 * Generate a fresh random keypair from a sideloaded seed.
 *
 * Returns secret key d in 384-bit shares d0, d1.
 *
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * This routine runs in constant time (except potentially waiting for entropy
 * from RND).
 *
 * @param[in]       w31: all-zero
 * @param[out] dmem[d0]: 1st private key share d0
 * @param[out] dmem[d1]: 2nd private key share d1
 * @param[out]  dmem[x]: Public key x-coordinate
 * @param[out]  dmem[y]: Public key y-coordinate
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
keypair_from_seed:
  /* Load keymgr seeds from WSRs.
       w20,w21 <= seed0
       w10,w11 <= seed1 */
  bn.wsrr   w20, KEY_S0_L
  bn.wsrr   w21, KEY_S0_H
  bn.wsrr   w10, KEY_S1_L
  bn.wsrr   w11, KEY_S1_H

  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, p384_key_from_seed

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal       x1, p384_base_mult

  ecall

.bss

/* Operational mode. */
.globl mode
.balign 4
mode:
  .zero 4

/* random scalar first share */
.globl k0
.balign 32
k0:
  .zero 64

/* random scalar second share */
.globl k1
.balign 32
k1:
  .zero 64

/* private key first share */
.globl d0
.balign 32
d0:
  .zero 64

/* private key second share */
.globl d1
.balign 32
d1:
  .zero 64

/* x-coordinate. */
.globl x
.balign 32
x:
  .zero 64

/* y-coordinate. */
.globl y
.balign 32
y:
  .zero 64

/* 704 bytes of scratchpad memory
  defined globally to save dmem */
.balign 32
.globl scratchpad
scratchpad:
  .zero 704
