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

.bss

/* Mode (1 = private key only) */
.balign 4
.globl mode
mode:
.zero 4

/**
 * Note: Software must write the full 512 bits of the seed values to avoid
 * runtime errors when OTBN tries to load the data with two 256-bit loads. Bits
 * above position 320 will be ignored.
 */

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
