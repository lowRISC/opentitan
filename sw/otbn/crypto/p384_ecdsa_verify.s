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
 * @param[in]  dmem[msg]: message to be verified
 * @param[in]    dmem[r]: r part of signature
 * @param[in]    dmem[s]: s part of signature
 * @param[in]    dmem[x]: x-coordinate of public key
 * @param[in]    dmem[y]: y-coordinate of public key
 * @param[out] dmem[x_r]: x1 coordinate to be compared to rs
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

/* result of verify (x1 coordinate) */
.globl x_r
.balign 32
x_r:
  .zero 64

.data

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
