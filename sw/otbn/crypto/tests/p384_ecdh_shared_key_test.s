/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone elliptic curve P-384 ECDH shared key generation test
 *
 * Uses OTBN ECC P-384 lib to perform a scalar multiplication with a valid
 * example curve point and an example scalar. Both scalar and coordinates of
 * the curve point are contained in the .data section below.
 * The x coordinate of the resulting curve point is masked arithmetically
 * with a random value. As the x coorodinate represents the actual
 * shared key, the x coordinate and its mask are then converted from an
 * arithmetic to a boolean masking scheme.
 *
 * The result of boolean unmasking is then compared with the expected shared
 * key value.
 */

.section .text.start

p384_ecdh_shared_key_test:
  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* fill gpp registers with pointers to relevant variables */
  /*la        x17, k0
  la        x19, k1
  la        x20, x
  la        x21, y

  /* call scalar point multiplication routine in P-384 lib */
  jal       x1, p384_scalar_mult

  /* load result to WDRs for unmasking and comparison with reference
     [w12,w11] <= dmem[p1_x] = x_m
     [w19,w18] <= dmem[p1_y] = m */
  li        x2, 11
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  li        x2, 18
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* Arithmetic to boolean conversion */
  jal       x1, p384_arithmetic_to_boolean_mod

  /* Boolean unmasking of result value
     [w21,w20] <= [w21,w20] ^ [w19,w18] */
  bn.xor    w0, w20, w18
  bn.xor    w1, w21, w19

  ecall
