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
  /* First, generate the masked secret key d and write to DMEM.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, run_gen_secret_key

  ecall

p256_gen_keypair:
  /* First, generate the masked secret key d and write to DMEM.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, run_gen_secret_key

  /* Generate the public key Q = d*G.
       dmem[x] <= Q.x
       dmem[y] <= Q.y */
  jal       x1, p256_base_mult

  ecall

run_gen_secret_key:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load shares of seed from DMEM.
       [w21,w20] <= dmem[seed0]
       [w11,w10] <= dmem[seed1] */
  li        x2, 20
  la        x3, seed0
  bn.lid    x2, 0(x3++)
  li        x2, 21
  bn.lid    x2, 0(x3)
  li        x2, 10
  la        x3, seed1
  bn.lid    x2, 0(x3++)
  li        x2, 11
  bn.lid    x2, 0(x3)

  /* Generate the derived secret key.
       [w21,w20] <= d0
       [w11,w10] <= d1 */
  jal       x1, p256_key_from_seed

  /* Write the results to DMEM.
       dmem[d0] <= [w21, w20]
       dmem[d1] <= [w11, w10] */
  li        x2, 20
  la        x3, d0
  bn.sid    x2, 0(x3++)
  li        x2, 21
  bn.sid    x2, 0(x3)
  li        x2, 10
  la        x3, d1
  bn.sid    x2, 0(x3++)
  li        x2, 11
  bn.sid    x2, 0(x3)

  ret

/**
 * Note: Technically this could be a .bss section, but it is convenient for
 * software to have zeroes already set on the high bits of the seeds.
 */
.data

/* Mode (1 = private key only, 2 = keypair) */
.balign 4
.globl mode
mode:
  .word 0x00000001

/* First share of seed (320 bits). */
.balign 32
.globl seed0
seed0:
  .word 0x2335f23f
  .word 0x3c174a16
  .word 0x128c1339
  .word 0xc48e8981
  .word 0x7843d9a2
  .word 0xbb6a0205
  .word 0x446984cc
  .word 0xa210c4be
  .word 0xd7c77320
  .word 0x2bac5b0b
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* Second share of seed (320 bits). */
.balign 32
.globl seed1
seed1:
  .word 0x225596d6
  .word 0x2df4bec0
  .word 0xbeb67c9e
  .word 0x6f2f939a
  .word 0xf7d1a873
  .word 0x99dd9f5a
  .word 0x551f77d1
  .word 0x17bcfeef
  .word 0x4e67f1f7
  .word 0x63e2e86d
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

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
