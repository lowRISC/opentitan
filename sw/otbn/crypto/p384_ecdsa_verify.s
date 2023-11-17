/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-384 ECDSA verifying operations.
 *
 * This binary verifies a signature. - !!! Attention !!! - before
 * signature verification p384_curve_point_valid
 * binary has to be executed to check if the provided
 * public key is valid.
 */

.section .text.start
.globl start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  jal       x1, ecdsa_verify

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp


/**
 * P-384 ECDSA signature verification
 *
 * The routine computes the x1 coordinate and places it in dmem. x1 will be
 * reduced (mod n), however, the final comparison has to be performed on the
 * host side. The signature is valid if x1 == r.
 * This routine runs in variable time.
 *
 * @param[in]  dmem[4]: dptr_rnd, pointer to dmem location where the reduced
 *                           affine x1-coordinate will be stored
 * @param[in]  dmem[8]: dptr_msg, pointer to the message to be verified in dmem
 * @param[in]  dmem[12]: dptr_r, pointer to r of signature in dmem
 * @param[in]  dmem[16]: dptr_s, pointer to s of signature in dmem
 * @param[in]  dmem[20]: dptr_x, pointer to x-coordinate of public key in dmem
 * @param[in]  dmem[20]: dptr_y, pointer to y-coordinate of public key in dmem
 * @param[out] dmem[rnd]: x1 coordinate to be compared to rs
 *
 * !!! Attention !!! - before signature verification p384_curve_point_valid
 * binary has to be executed to check if the provided public key is valid.
 *
 */
ecdsa_verify:
  /* Verify the signature (compute x1). */
  jal      x1, p384_verify

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

/* pointer to rnd (dptr_rnd) */
.globl dptr_rnd
dptr_rnd:
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

/* result of verify (x1 coordinate) */
.globl rnd
.balign 32
rnd:
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

/* 896 bytes of scratchpad memory
  defined globally to save dmem. */
.balign 32
.globl scratchpad
scratchpad:
  .zero 896
