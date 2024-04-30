/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-384 ECDSA key generation operations.
 *
 * This binary generates a new keypair.
 */

.section .text.start
.globl start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  jal       x1, random_keygen

  /* Invalid mode; fail. */
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
random_keygen:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, p384_generate_random_key

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal       x1, p384_base_mult

  ecall

.bss

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
