/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone unit tests for point addition of extended twisted Edwards
 * coordinates for Ed25519.
 *
 * Tests included in this file are intended for quick sanity-checks of
 * subroutines; they will not cover all edge cases.
 *
 * This test will exit with the number of failures written to the w0 register;
 * w0=0 means all tests succeeded.
 */

.section .text.start

main:
  /* Prepare all-zero register. */
  bn.xor  w31, w31, w31

  /* Setup for coordinate field arithmetic. */
  jal     x1, fe_init

  /* w30 <= 38 */
  bn.addi w30, w31, 38

  /* Initialize failure counter to 0. */
  bn.mov  w0, w31

  /* w29 <= (2*d) mod p. */
  li      x2, 29
  la      x3, two_d
  bn.lid  x2, 0(x3)

  /* Run tests. */
  jal     x1, run_ext_add_test
  jal     x1, run_ext_scmul_zero_test
  jal     x1, run_ext_scmul_order_test
  jal     x1, run_ext_scmul_base_test

  ecall

/**
 * Check that P + origin = P.
 *
 * Increment failure counter if the test fails. In extended twisted Edwards
 * coordinates, the identity is (0, Z, Z, 0) for any non-zero Z (as described in
 * RFC 8032, section 5.1.4).
 *
 * @param[in]     w19: constant, 19
 * @param[in]     MOD: p, modulus = 2^255 - 19
 * @param[in]     w29: constant, (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]     w30: constant, 38
 * @param[in]     w31: all-zero
 * @param[in,out] w0:  test failure counter
 *
 * clobbered registers: w4 to w7, w10 to w18, w20 to w23, w24 to w27
 * clobbered flag groups: FG0
 */
run_ext_add_test:
  /* Construct origin point (0, 1, 1, 0) in registers w10 to w13. */
  bn.mov  w10, w31
  bn.addi w11, w31, 1
  bn.addi w12, w31, 1
  bn.mov  w13, w31

  /* Load test point P into registers w14 to w17. */

  /* w14 <= dmem[p_x] */
  li      x2, 14
  la      x3, p_x
  bn.lid  x2++, 0(x3)
  /* w15 <= dmem[p_y] */
  la      x3, p_y
  bn.lid  x2++, 0(x3)
  /* w16 <= dmem[p_z] */
  la      x3, p_z
  bn.lid  x2++, 0(x3)
  /* w17 <= dmem[p_t] */
  la      x3, p_t
  bn.lid  x2++, 0(x3)

  /* Call ext_add.
       [w13:w10] <= (0, 1, 1, 0) + P */
  jal     x1, ext_add

  /* Check if the result is equivalent to P.
       w4 <= 1 if [w13:w10] equivalent to P else 0 */
  jal     x1, ext_equal

  /* Invert the single-bit result of the check.
     w4 <= (~w4) & 1 = 0 if w4 else 1 */
  bn.not  w4, w4
  bn.addi w5, w31, 1
  bn.and  w4, w4, w5

  /* Increment failure counter if the test failed.
     w0 <= w0 + w4 */
  bn.add  w0, w0, w4

  ret

/**
 * Check that 0 * P = origin.
 *
 * Increment failure counter if the test fails.
 *
 * @param[in]     w19: constant, w19 = 19
 * @param[in]     MOD: p, modulus = 2^255 - 19
 * @param[in]     w30: constant, w30 = (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]     w31: all-zero
 * @param[in,out] w0:  test failure counter
 *
 * clobbered registers: TODO
 * clobbered flag groups: FG0
 */
run_ext_scmul_zero_test:
  /* Initialize scalar input to 0.
       w28 <= 0 */
  bn.mov   w28, w31

  /* Load test point P into registers w6 to w9. */

  /* w6 <= dmem[p_x] */
  li      x2, 6
  la      x3, p_x
  bn.lid  x2++, 0(x3)
  /* w7 <= dmem[p_y] */
  la      x3, p_y
  bn.lid  x2++, 0(x3)
  /* w8 <= dmem[p_z] */
  la      x3, p_z
  bn.lid  x2++, 0(x3)
  /* w9 <= dmem[p_t] */
  la      x3, p_t
  bn.lid  x2++, 0(x3)

  /* Call ext_scmul.
       [w13:w10] <= 0 * P */
  jal     x1, ext_scmul

  /* Construct origin point (0, 1, 1, 0) in registers w14 to w17. */
  bn.mov  w14, w31
  bn.addi w15, w31, 1
  bn.addi w16, w31, 1
  bn.mov  w17, w31

  /* Check if the result is equivalent to P.
       w4 <= 1 if [w13:w10] equivalent to [w14:w17] else 0 */
  jal     x1, ext_equal

  /* Invert the single-bit result of the check.
     w4 <= (~w4) & 1 = 0 if w4 else 1 */
  bn.not  w4, w4
  bn.addi w5, w31, 1
  bn.and  w4, w4, w5

  /* Increment failure counter if the test failed.
     w0 <= w0 + w4 */
  bn.add  w0, w0, w4

  ret

/**
 * Check that (L - 1) * P + P + P = P.
 *
 * Increment failure counter if the test fails.  Because L is the group order,
 * it should be the case that L * P = origin and (L + 1) * P = P. We compute (L
 * + 1) * P as (L - 1) * P + P + P because (L - 1) * P is the maximum scalar
 * value.
 *
 * @param[in]     w19: constant, w19 = 19
 * @param[in]     MOD: p, modulus = 2^255 - 19
 * @param[in]     w30: constant, w30 = (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]     w31: all-zero
 * @param[in,out] w0:  test failure counter
 *
 * clobbered registers: TODO
 * clobbered flag groups: FG0
 */
run_ext_scmul_order_test:
  /* Load the scalar value L - 1.
       w28 <= dmem[L_minus1] = L - 1 */
  li       x2, 28
  la       x3, L_minus1
  bn.lid   x2, 0(x3)

  /* Load test point P into registers w6 to w9. */

  /* w6 <= dmem[p_x] */
  li       x2, 6
  la       x3, p_x
  bn.lid   x2++, 0(x3)
  /* w7 <= dmem[p_y] */
  la       x3, p_y
  bn.lid   x2++, 0(x3)
  /* w8 <= dmem[p_z] */
  la       x3, p_z
  bn.lid   x2++, 0(x3)
  /* w9 <= dmem[p_t] */
  la       x3, p_t
  bn.lid   x2++, 0(x3)

  /* Call ext_scmul.
       [w13:w10] <= w28 * [w9:w6] = (L - 1) * P */
  jal      x1, ext_scmul

  /* Copy test point P into registers w14 to w17. */
  bn.mov   w14, w6
  bn.mov   w15, w7
  bn.mov   w16, w8
  bn.mov   w17, w9

  /* [w13:w10] <= [w13:w10] + [w17:14] = L * P */
  jal      x1, ext_add
  /* [w13:w10] <= [w13:w10] + [w17:14] = (L + 1) * P */
  jal      x1, ext_add

  /* Check if the result is equivalent to P.
       w4 <= 1 if [w13:w10] equivalent to [w14:w17] else 0 */
  jal      x1, ext_equal

  /* Invert the single-bit result of the check.
     w4 <= (~w4) & 1 = 0 if w4 else 1 */
  bn.not   w4, w4
  bn.addi  w5, w31, 1
  bn.and   w4, w4, w5

  /* Increment failure counter if the test failed.
     w0 <= w0 + w4 */
  bn.add   w0, w0, w4

  ret

/**
 * Regression test using data from RFC 8032.
 *
 * This test multiplies the base point B by the (precomputed) value r mod L
 * from RFC 8032, section 7.1, test 1.
 *
 * Increments failure counter if the test fails.
 *
 * @param[in]     w19: constant, w19 = 19
 * @param[in]     MOD: p, modulus = 2^255 - 19
 * @param[in]     w30: constant, w30 = (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]     w31: all-zero
 * @param[in,out] w0:  test failure counter
 *
 * clobbered registers: TODO
 * clobbered flag groups: FG0
 */
run_ext_scmul_base_test:
  /* Load the scalar value r mod L.
       w28 <= dmem[rfc_test1_rmodL] = r mod L */
  li       x2, 28
  la       x3, rfc_test1_rmodL
  bn.lid   x2, 0(x3)

  /* Load the base point B (in affine coordinates).
       w6 <= dmem[ed25519_Bx] = B.x
       w7 <= dmem[ed25519_By] = B.y */
  li       x2, 6
  la       x3, ed25519_Bx
  bn.lid   x2++, 0(x3)
  la       x3, ed25519_By
  bn.lid   x2, 0(x3)

  /* Convert B to extended coordinates.
       [w9:w6] <= extended(B) = (B.X, B.Y, B.Z, B.T) */
  bn.addi  w8, w31, 1
  bn.mov   w22, w6
  bn.mov   w23, w7
  jal      x1, fe_mul
  bn.mov   w9, w22

  /* Compute the signature point R = [r]B.
       [w13:w10] <= w28 * [w9:w6] = r * B */
  jal      x1, ext_scmul

  /* Load the expected result R (in affine coordinates).
       w14 <= dmem[rfc_test1_Rx] = R.x
       w15 <= dmem[rfc_test1_Ry] = R.y */
  li       x2, 14
  la       x3, rfc_test1_Rx
  bn.lid   x2++, 0(x3)
  la       x3, rfc_test1_Ry
  bn.lid   x2, 0(x3)

  /* Convert R to extended coordinates.
       [w17:w14] <= extended(R) = (R.X, R.Y, R.Z, R.T) */
  bn.addi  w16, w31, 1
  bn.mov   w22, w14
  bn.mov   w23, w15
  jal      x1, fe_mul
  bn.mov   w17, w22

  /* Check if the computed R matches the expected R.
       w4 <= 1 if [w13:w10] equivalent to [w17:w14] else 0 */
  jal      x1, ext_equal

  /* Invert the single-bit result of the check.
     w4 <= (~w4) & 1 = 0 if w4 else 1 */
  bn.not   w4, w4
  bn.addi  w5, w31, 1
  bn.and   w4, w4, w5

  /* Increment failure counter if the test failed.
     w0 <= w0 + w4 */
  bn.add   w0, w0, w4

  ret

/**
 * Check if two points in extended coordinates are equal.
 *
 * Returns 1 if (X1, Y1, Z1, T1) is equivalent to (X2, Y2, Z2, T2), otherwise
 * returns 0.
 *
 * As per RFC 8032, returns 1 iff:
 *   (X1 * Z2 - X2 * Z1) mod p = 0, and
 *   (Y1 * Z2 - Y2 * Z2) mod p = 0.
 *
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]  w10: input X1 (X1 < p)
 * @param[in]  w11: input Y1 (Y1 < p)
 * @param[in]  w12: input Z1 (Z1 < p)
 * @param[in]  w13: input T1 (T1 < p)
 * @param[in]  w14: input X2 (X2 < p)
 * @param[in]  w15: input Y2 (Y2 < p)
 * @param[in]  w16: input Z2 (Z2 < p)
 * @param[in]  w17: input T2 (T2 < p)
 * @param[in]  w31: all-zero
 * @param[out] w4: result, 1 or 0
 *
 * clobbered registers: w4 to w7
 * clobbered flag groups: FG0
 */
ext_equal:
  /* w5 <= 1 */
  bn.addi  w5, w31, 1

  /* Compute (X1 * Z2). */

  /* w22 <= w10 = X1 */
  bn.mov   w22, w10
  /* w23 <= w16 = Z2 */
  bn.mov   w23, w16
  /* w22 <= w22 * w23 = X1 * Z2 */
  jal      x1, fe_mul
  /* w6 <= w22 <= X1 * Z2 */
  bn.mov   w6, w22

  /* Compute (X2 * Z1). */

  /* w22 <= w14 = X2 */
  bn.mov   w22, w14
  /* w23 <= w12 = Z1 */
  bn.mov   w23, w12
  /* w22 <= w22 * w23 = X2 * Z1 */
  jal      x1, fe_mul

  /* First check. */

  /* w6 <= w6 - w22 <= (X1 * Z2) - (X2 * Z1) */
  bn.sub  w6, w6, w22
  /* w7 <= w5 if FG0.Z else w31 = 1 iff first check passed */
  bn.sel   w7, w5, w31, FG0.Z

  /* Compute (Y1 * Z2). */

  /* w22 <= w11 = Y1 */
  bn.mov   w22, w11
  /* w23 <= w16 = Z2 */
  bn.mov   w23, w16
  /* w22 <= w22 * w23 = Y1 * Z2 */
  jal      x1, fe_mul
  /* w6 <= w22 <= Y1 * Z2 */
  bn.mov   w6, w22

  /* Compute (Y2 * Z1). */

  /* w22 <= w15 = Y2 */
  bn.mov   w22, w15
  /* w23 <= w12 = Z1 */
  bn.mov   w23, w12
  /* w22 <= w22 * w23 = Y2 * Z1 */
  jal      x1, fe_mul

  /* Second check. */

  /* w6 <= w6 - w22 <= (Y1 * Z2) - (Y2 * Z1) */
  bn.sub  w6, w6, w22
  /* w4 <= w5 if FG0.Z else w31 = 1 iff second check passed */
  bn.sel   w4, w5, w31, FG0.Z

  /* w4 <= w4 & w7 = check1 & check2 */
  bn.and   w4, w4, w7
  ret

.data

/* Constant (2*d) mod p where d=(-121665/121666) mod p. */
.balign 32
two_d:
  .word 0x26b2f159
  .word 0xebd69b94
  .word 0x8283b156
  .word 0x00e0149a
  .word 0xeef3d130
  .word 0x198e80f2
  .word 0x56dffce7
  .word 0x2406d9dc

/* Randomly-generated point P = (X, Y, Z, T) for testing. */

.balign 32
p_x:
  .word 0xfb26b8ad
  .word 0x985868f2
  .word 0x959024ff
  .word 0xad05713d
  .word 0x4c13236f
  .word 0x4cb962fa
  .word 0x94e3ec9b
  .word 0x6cb4791c

.balign 32
p_y:
  .word 0x02ddf0f9
  .word 0x12939d50
  .word 0xb60b8772
  .word 0xf4a2fd69
  .word 0x83e01450
  .word 0x35358712
  .word 0xe23a98a7
  .word 0x111d76fb

.balign 32
p_z:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

.balign 32
p_t:
  .word 0xa1f92700
  .word 0x90a4e7b8
  .word 0x050bc191
  .word 0x6fc656c2
  .word 0x2b780407
  .word 0x349b3769
  .word 0x879cdac2
  .word 0x588b3f8e

/* Constant L-1 (where L is the scalar field modulus) */
.balign 32
L_minus1:
  .word 0x5cf5d3ec
  .word 0x5812631a
  .word 0xa2f79cd6
  .word 0x14def9de
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x10000000

/* Value of (r mod L) for RFC 8032, section 7.1, test 1. */
.balign 32
rfc_test1_rmodL:
  .word 0x300789f3
  .word 0xea3d898c
  .word 0x7d7844f2
  .word 0x6853afb4
  .word 0x74104922
  .word 0xedc2af18
  .word 0xac758fc5
  .word 0x0474a058

/* Affine x coordinate of base point B (see RFC 8032, section 5.1). */
.balign 32
ed25519_Bx:
  .word 0x8f25d51a
  .word 0xc9562d60
  .word 0x9525a7b2
  .word 0x692cc760
  .word 0xfdd6dc5c
  .word 0xc0a4e231
  .word 0xcd6e53fe
  .word 0x216936d3

/* Affine y coordinate of base point B (see RFC 8032, section 5.1). */
.balign 32
ed25519_By:
  .word 0x66666658
  .word 0x66666666
  .word 0x66666666
  .word 0x66666666
  .word 0x66666666
  .word 0x66666666
  .word 0x66666666
  .word 0x66666666

/* Expected affine x coordinate for R = [r]B in RFC 8032, section 7.1, test 1
   = 0x6218e309d40065fcc338b3127f46837182324bd01ce6f3cf81ab44e62959c82a */
.balign 32
rfc_test1_Rx:
  .word 0x2959c82a
  .word 0x81ab44e6
  .word 0x1ce6f3cf
  .word 0x82324bd0
  .word 0x7f468371
  .word 0xc338b312
  .word 0xd40065fc
  .word 0x6218e309

/* Expected affine y coordinate for R = [r]B in RFC 8032, section 7.1, test 1
   = 0x5501492265e073d874d9e5b81e7f87848a826e80cce2869072ac60c3004356e5 */
.balign 32
rfc_test1_Ry:
  .word 0x004356e5
  .word 0x72ac60c3
  .word 0xcce28690
  .word 0x8a826e80
  .word 0x1e7f8784
  .word 0x74d9e5b8
  .word 0x65e073d8
  .word 0x55014922
