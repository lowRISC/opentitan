/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Wrapper specifically for SCA/formal analysis of p256 keygen.
 *
 * Normally, the key generation routines called here would be used with key
 * manager seeds only. This wrapper uses software-provided seeds for analysis
 * purposes and should not be used for production code.
 */

.section .text.start

start:
  /* Read mode, then tail-call either p256_gen_secret_key or p256_gen_keypair */
  la    x2, mode
  lw    x2, 0(x2)

  li    x3, 1
  beq   x2, x3, p256_gen_secret_key

  li    x3, 2
  beq   x2, x3, p256_gen_keypair

  /* Invalid mode; fail. */
  unimp

p256_gen_secret_key:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load shares of seed from DMEM.
       [w21,w20] <= dmem[seed0]
       [w23,w33] <= dmem[seed1] */
  li        x2, 20
  la        x3, seed0
  bn.lid    x2, 0(x3++)
  li        x2, 21
  bn.lid    x2++, 0(x3)
  la        x3, seed1
  bn.lid    x2, 0(x3++)
  li        x2, 23
  bn.lid    x2, 0(x3)

  /* Generate the derived secret key.
       [w21,w20] <= d0
       [w23,w33] <= d1 */
  jal       x1, p256_key_from_seed

  /* Write the results to DMEM.
       dmem[d0] <= [w21, w20]
       dmem[d1] <= [w23, w22] */
  li        x2, 20
  la        x3, d0
  bn.sid    x2, 0(x3++)
  li        x2, 21
  bn.lid    x2++, 0(x3)
  la        x3, d1
  bn.lid    x2, 0(x3++)
  li        x2, 23
  bn.lid    x2, 0(x3)

  ecall

p256_gen_keypair:
  /* First, generate the masked secret key d and write to DMEM.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, p256_gen_secret_key

  /* Generate the public key Q = d*G.
       dmem[x] <= Q.x
       dmem[y] <= Q.y */
  jal       x1, p256_base_mult

  ecall


/**
 * Note: Technically this could be a .bss section, but it is convenient for
 * software to have zeroes already set on the high bits of the seeds.
 */
.data

/* Mode (1 = private key only, 2 = keypair) */
.balign 4
.globl mode
mode:
.zero 4

/* First share of seed (320 bits). */
.balign 32
.globl seed0
seed0:
.zero 64

/* Second share of seed (320 bits). */
.balign 32
.globl seed1
seed1:
.zero 64

/* First share of output key (320 bits). */
.balign 32
.globl d0
d0:
.zero 64

/* Second share of output key (320 bits). */
.balign 32
.globl d1
d1:
.zero 64

/* x-coordinate of output public key (256 bits). */
.balign 32
.globl x
x:
.zero 32

/* y-coordinate of output public key (256 bits). */
.balign 32
.globl y
y:
.zero 32
