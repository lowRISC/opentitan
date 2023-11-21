/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-256 ECDSA sign test
 *
 * Uses OTBN ECC P-256 lib to perform an ECDSA signing operation.
 * An example message digest, the private signing key and a random value k are
 * provided in the .data section below. Note that this test does not yet use
 * OTBN's entropy interface as a source for the random value in the ECDSA
 * operation.
 *
 * Resulting R and S of the signature are copied to the wide registers. See
 * comment at the end of the file for expected values.
 */

.section .text.start

ecdsa_sign_test:
  /* Randomize all shares.
       dmem[k0] <= randomize(dmem[k0])
       dmem[k1] <= randomize(dmem[k1])
       dmem[d0] <= randomize(dmem[d0])
       dmem[d1] <= randomize(dmem[d1]) */
  la       x16, k0
  jal      x1, randomize_share
  la       x16, k1
  jal      x1, randomize_share
  la       x16, d0
  jal      x1, randomize_share
  la       x16, d1
  jal      x1, randomize_share

  /* call ECDSA signing subroutine in P-256 lib */
  jal      x1, p256_sign

  /* load signature to wregs for comparison with reference */
  li        x2, 0
  la        x3, r
  bn.lid    x2, 0(x3)
  li        x2, 1
  la        x3, s
  bn.lid    x2, 0(x3)

  ecall

/**
 * Produce a 320-bit share representing a 256-bit value modulo n.
 *
 * Returns y = (x + r * n),
 *   where r is a 63-bit pseudorandom number and n is the P-256 curve order.
 *
 * Reads input from DMEM and stores back to the same location.
 *
 * @param[in]        x16: x_ptr, DMEM location of input
 * @param[in]  dmem[x16]: x, input (256 bits)
 * @param[out] dmem[x16]: y, output (320 bits)
 *
 * clobbered registers: w0 to w5
 * clobbered flag groups: FG0
 */
randomize_share:
  /* Initialize all-zero register. */
  bn.xor  w31, w31, w31

  /* Load input.
       w4 <= dmem[x16] = x */
  li        x2, 4
  bn.lid    x2, 0(x16)

  /* Get a 63-bit pseudorandom number.
       w0 <= URND()[255:193] = r */
  bn.wsrr  w0, URND
  bn.rshi  w0, w31, w0 >> 193

  /* Load the curve order n.
     w1 <= dmem[p256_n] = n */
  li        x2, 1
  la        x3, p256_n
  bn.lid    x2, 0(x3)

  /* w2,w3 <= w0 * w1 = r * n */
  bn.mulqacc.z         w0.0, w1.0, 0
  bn.mulqacc.so  w2.L, w0.0, w1.1, 64
  bn.mulqacc           w0.0, w1.2, 0
  bn.mulqacc.so  w2.U, w0.0, w1.3, 64
  bn.mulqacc.wo    w3, w31.0, w31.0, 0

  /* Add to input.
       w4, w5 <= w4 + [w2,w3] = x + r * n */
  bn.add  w4, w4, w2
  bn.addc w5, w31, w3

  /* Store randomized share (320 bits).
       dmem[x16] <= [w4,w5] = x + r * n */
  li        x2, 4
  bn.sid    x2, 0(x16++)
  li        x2, 5
  bn.sid    x2, 0(x16)

  ret

.data

/* first share of nonce k (first 128 bits of k, then all 0s) */
.globl k0
.balign 32
k0:
  .word 0xfe6d1071
  .word 0x21d0a016
  .word 0xb0b2c781
  .word 0x9590ef5d
  .zero 16
  .zero 32

/* second share of nonce k (128 0s, then last 128 bits of k, then all 0s) */
.globl k1
.balign 32
k1:
  .zero 16
  .word 0x3fdfa379
  .word 0x1b76ebe8
  .word 0x74210263
  .word 0x1420fc41
  .zero 32

/* message digest */
.globl msg
.balign 32
msg:
  .word 0x4456fd21
  .word 0x400bdd7d
  .word 0xb54d7452
  .word 0x17d015f1
  .word 0x90d4d90b
  .word 0xb028ad8a
  .word 0x6ce90fef
  .word 0x06d71207

/* first share of private key d (first 128 bits of d, then all 0s) */
.globl d0
.balign 32
d0:
  .word 0xc7df1a56
  .word 0xfbd94efe
  .word 0xaa847f52
  .word 0x2d869bf4
  .zero 16
  .zero 32

/* second share of private key d (128 0s, then last 128 bits of d, then all 0s) */
.globl d1
.balign 32
d1:
  .zero 16
  .word 0x543b963b
  .word 0xe5f2cbee
  .word 0x9144233d
  .word 0xc0fbe256
  .zero 32

/* signature R */
.globl r
.balign 32
r:
  .zero 32

/* signature S */
.globl s
.balign 32
s:
  .zero 32
