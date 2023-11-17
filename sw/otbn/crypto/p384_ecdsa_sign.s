/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-384 ECDSA signing operations.
 *
 * This binary generates a signature using a caller-provided secret key.
 */

.section .text.start
.globl start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  jal       x1, ecdsa_sign

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp

/**
 * P-384 ECDSA signature generation.
 * Generate the secret scalar k from a random seed.
 *
 * @param[in]  dmem[0]: dptr_k0, pointer to location in dmem containing
 *                      1st scalar share k0
 * @param[in]  dmem[4]: dptr_k1, pointer to location in dmem containing
 *                      2nd scalar share k1
 * @param[in]  dmem[8]: dptr_msg, pointer to the message to be signed in dmem
 * @param[in]  dmem[12]: dptr_r, pointer to dmem location where s component
 *                               of signature will be placed
 * @param[in]  dmem[16]: dptr_s, pointer to dmem location where r component
 *                               of signature will be placed
 * @param[in]  dmem[28]: dptr_d0, pointer to location in dmem containing
 *                      1st private key share d0
 * @param[in]  dmem[32]: dptr_d1, pointer to location in dmem containing
 *                      2nd private key share d1
 * @param[out] dmem[r]: r component of signature
 * @param[out] dmem[s]: s component of signature
 */
ecdsa_sign:
  /* Generate a fresh random scalar for signing.
       dmem[k0] <= first share of k
       dmem[k1] <= second share of k */
  jal      x1, p384_generate_k

  /* Generate the signature. */
  jal      x1, p384_sign

  ecall

.bss

/* pointer to x-coordinate (dptr_x) */
.globl dptr_x
.balign 4
dptr_x:
  .zero 4

/* pointer to y-coordinate (dptr_y) */
.globl dptr_y
.balign 4
dptr_y:
  .zero 4

/* pointer to k0 (dptr_k0) */
.globl dptr_k0
dptr_k0:
  .zero 4

/* pointer to k1 (dptr_k1) */
.globl dptr_k1
dptr_k1:
  .zero 4

/* pointer to d0 (dptr_d0) */
.globl dptr_d0
dptr_d0:
  .zero 4

/* pointer to d1 (dptr_d1) */
.globl dptr_d1
dptr_d1:
  .zero 4

/* pointer to msg (dptr_msg) */
.globl dptr_msg
dptr_msg:
  .zero 4

/* pointer to R (dptr_r) */
.globl dptr_r
dptr_r:
  .zero 4

/* pointer to S (dptr_s) */
.globl dptr_s
dptr_s:
  .zero 4

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

/* hash message to sign/verify */
.globl msg
.balign 32
msg:
  .zero 64

/* r part of signature */
.globl r
.balign 32
r:
  .zero 64

/* s part of signature */
.globl s
.balign 32
s:
  .zero 64

/* 704 bytes of scratchpad memory
  defined globally to save dmem */
.balign 32
.globl scratchpad
scratchpad:
  .zero 704
