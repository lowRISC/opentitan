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
 * @param[in]   dmem[k0]: 1st scalar share k0
 * @param[in]   dmem[k1]: 2nd scalar share k1
 * @param[in]  dmem[msg]: message to be signed in dmem
 * @param[in]   dmem[d0]: 1st private key share d0
 * @param[in]   dmem[d1]: 2nd private key share d1
 * @param[out]   dmem[r]: r component of signature
 * @param[out]   dmem[s]: s component of signature
 */
ecdsa_sign:
  /* Generate a fresh random scalar for signing.
       dmem[k0] <= first share of k
       dmem[k1] <= second share of k */
  jal      x1, p384_generate_k

  /* Fill gpp registers with pointers to variables required for p384_sign */
  /* scalar shares */
  /*la        x17, k0
  la        x19, k1
  /* message */
  /*la        x6, msg
  /* signature values */
  /*la        x14, r
  la        x15, s
  /* secret key shares */
  /*la        x4, d0
  la        x5, d1

  /* Generate the signature. */
  jal      x1, p384_sign

  ecall

.bss

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

.data

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

/* 704 bytes of scratchpad memory
  defined globally to save dmem */
.balign 32
.globl scratchpad
scratchpad:
  .zero 704
