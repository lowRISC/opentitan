/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone unit tests for point encoding/decoding for Ed25519.
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
  bn.xor w31, w31, w31

  /* MOD <= dmem[modulus] = p */
  li      x2, 2
  la      x3, modulus
  bn.lid  x2, 0(x3)
  bn.wsrw 0x0, w2

  /* w19 <= 19 */
  bn.addi w19, w31, 19

  /* Initialize failure counter to 0. */
  bn.mov  w0, w31

  /* w30 <= dmem[ed25519_d] = d (curve parameter) */
  li      x2, 30
  la      x3, ed25519_d
  bn.lid  x2, 0(x3)

  /* Run tests. */
  jal     x1, run_encode_decode_test
  jal     x1, run_rfc_decode_test

  ecall

/**
 * Encode, then decode the test point and check against starting value.
 *
 * Increment failure counter if the test fails.
 *
 * @param[in]     w19: constant, w19 = 19
 * @param[in]     MOD: p, modulus = 2^255 - 19
 * @param[in]     w30: constant, w30 = (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]     w31: all-zero
 * @param[in,out] w0:  test failure counter
 *
 * clobbered registers: w4 to w6, w10 to w18, w20 to w23, w24 to w27
 * clobbered flag groups: FG0
 */
run_encode_decode_test:
  /* Load test point P into registers w8 and w9. */

  /* w8 <= dmem[p_x] */
  li      x2, 8
  la      x3, p_x
  bn.lid  x2++, 0(x3)
  /* w9 <= dmem[p_y] */
  la      x3, p_y
  bn.lid  x2, 0(x3)

  /* Call affine_encode.
       w11 <= encode(P) */
  bn.mov  w10, w8
  bn.mov  w11, w9
  jal     x1, affine_encode

  /* Call affine_decode.
       [w10,w11] <= decode(encode(P))
       x20 <= SUCCESS or FAILURE */
  jal     x1, affine_decode_var

  /* Load the SUCCESS magic value. */
  li      x2, 0xf77fe650

  /* If decoding did not succeed, increment the failure counter and finish. */
  bne     x20, x2, encode_decode_failed

  /* Check if the result is equivalent to P.
       w4 <= 1 if [w11:w10] equivalent to P else 0 */
  jal     x1, affine_equal

  /* Invert the single-bit result of the check.
     w4 <= (~w4) & 1 = 0 if w4 else 1 */
  bn.not  w4, w4
  bn.addi w5, w31, 1
  bn.and  w4, w4, w5

  /* Increment failure counter if the test failed.
     w0 <= w0 + w4 */
  bn.add  w0, w0, w4

  ret

  encode_decode_failed:
  /* Increment failure counter and return. */
  bn.addi  w0, w0, 1
  ret

/**
 * Decode the public key point from RFC 8032, section 7.1, test 1.
 *
 * Increment failure counter if the test fails.
 *
 * @param[in]     w19: constant, w19 = 19
 * @param[in]     MOD: p, modulus = 2^255 - 19
 * @param[in]     w30: constant, w30 = (2*d) mod p, d = (-121665/121666) mod p
 * @param[in]     w31: all-zero
 * @param[in,out] w0:  test failure counter
 *
 * clobbered registers: w4 to w6, w10 to w18, w20 to w23, w24 to w27
 * clobbered flag groups: FG0
 */
run_rfc_decode_test:
  /* Load encoded point.
       w11 <= dmem[test1_A_enc] */
  li      x2, 11
  la      x3, test1_A_enc
  bn.lid  x2, 0(x3)

  /* Call affine_decode.
       [w10,w11] <= decode(encode(P))
       x20 <= SUCCESS or FAILURE */
  jal     x1, affine_decode_var

  /* Load the SUCCESS magic value. */
  li      x2, 0xf77fe650

  /* If decoding did not succeed, increment the failure counter and finish. */
  bne     x20, x2, rfc_decode_failed

  /* Load the expected decoded value.*/

  /* w8 <= dmem[test1_Ax] */
  li      x2, 8
  la      x3, test1_Ax
  bn.lid  x2++, 0(x3)
  /* w9 <= dmem[test1_Ay] */
  la      x3, test1_Ay
  bn.lid  x2, 0(x3)

  /* Check if the resulting point is correct.
       w4 <= 1 if [w11:w10] equivalent to [w9:w8] else 0 */
  jal     x1, affine_equal

  /* Invert the single-bit result of the check.
     w4 <= (~w4) & 1 = 0 if w4 else 1 */
  bn.not  w4, w4
  bn.addi w5, w31, 1
  bn.and  w4, w4, w5

  /* Increment failure counter if the test failed.
     w0 <= w0 + w4 */
  bn.add  w0, w0, w4

  ret

  rfc_decode_failed:
  /* Increment failure counter and return. */
  bn.addi  w0, w0, 1
  ret

/**
 * Check if two points in affine coordinates are equal.
 *
 * Returns 1 if (x1, y1) is equivalent to (x2, y2), otherwise returns 0.
 *
 * All coordinates are assumed to be fully reduced modulo p, so this check is
 * just ((x1 == y1) && (x2 == y2)).
 *
 * @param[in]  w19: constant, w19 = 19
 * @param[in]  MOD: p, modulus = 2^255 - 19
 * @param[in]   w8: input x1 (x1 < p)
 * @param[in]   w9: input y1 (y1 < p)
 * @param[in]  w10: input x2 (x2 < p)
 * @param[in]  w11: input y2 (y2 < p)
 * @param[in]  w31: all-zero
 * @param[out]  w4: result, 1 or 0
 *
 * clobbered registers: w5, w6
 * clobbered flag groups: FG0
 */
affine_equal:
  /* w5 <= 1 */
  bn.addi  w5, w31, 1

  /* FG0.Z <= (w8 - w10 == 0) = (x1 == y1)  */
  bn.cmp   w8, w10
  /* w6 <= w5 if FG0.Z else w31 = (x1 == y1) */
  bn.sel   w6, w5, w31, FG0.Z

  /* FG0.Z <= (w9 - w11 == 0) = (x2 == y2)  */
  bn.cmp   w9, w11
  /* w4 <= w5 if FG0.Z else w31 = (x2 == y2) */
  bn.sel   w4, w5, w31, FG0.Z

  /* w4 <= w6 & w4 = (x1 == y1) & (x2 == y2) */
  bn.and   w4, w4, w6
  ret

.data

/* Modulus p = 2^255 - 19. */
.balign 32
modulus:
  .word 0xffffffed
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
  .word 0x7fffffff

/* Constant d where d=(-121665/121666) mod p (from RFC 8032 section 5.1) */
.balign 32
ed25519_d:
  .word 0x135978a3
  .word 0x75eb4dca
  .word 0x4141d8ab
  .word 0x00700a4d
  .word 0x7779e898
  .word 0x8cc74079
  .word 0x2b6ffe73
  .word 0x52036cee

/* Randomly-generated point P = (x, y) for testing. */

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

/* Encoded public key from RFC 8032, section 7.1, test 1. */
test1_A_enc:
  .word 0x01985ad7
  .word 0xb70ab182
  .word 0xd3fe4bd5
  .word 0x3a0764c9
  .word 0xf372e10e
  .word 0x2523a6da
  .word 0x681a02af
  .word 0x1a5107f7

/* Expected decoded y coordinate from test1_A_enc. */
test1_Ay:
  .word 0x01985ad7
  .word 0xb70ab182
  .word 0xd3fe4bd5
  .word 0x3a0764c9
  .word 0xf372e10e
  .word 0x2523a6da
  .word 0x681a02af
  .word 0x1a5107f7

/* Expected recovered x coordinate from test1_A_enc. */
test1_Ax:
  .word 0x777645ce
  .word 0xb12786bd
  .word 0x53187c24
  .word 0xc513d472
  .word 0x60d0f620
  .word 0x2297e08d
  .word 0x2b9d3429
  .word 0x55d0e09a
