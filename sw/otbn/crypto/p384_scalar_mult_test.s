/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-384 scalar multiplication
 *
 * Performs multiplication of a P-384 curve point by a scalar. Both, the
 * scalar and the affine coordinates of the point are contained in the
 * .data section below.
 *
 * See comment at the end of the file for expected values of coordinates
 * of resulting point.
 */

.section .text.start

p384_scalar_mult_test:

  /* set dmem pointer to point to x-coordinate */
  la       x2, p1_x
  la       x3, dptr_x
  sw       x2, 0(x3)

  /* set dmem pointer to point to y-coordinate */
  la       x2, p1_y
  la       x3, dptr_y
  sw       x2, 0(x3)

  /* set dmem pointer to point to scalar k */
  la       x2, scalar
  la       x3, dptr_k
  sw       x2, 0(x3)

  /* set dmem pointer to point to blinding parameter */
  la       x2, blinding_param
  la       x3, dptr_rnd
  sw       x2, 0(x3)

  /* call scalar point multiplication routine in P-384 lib */
  jal      x1, scalar_mult_p384

  /* load result to WDRs for comparison with reference */
  li        x2, 0
  la        x3, p1_x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  la        x3, p1_y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  ecall


.section .data

/* point 1 x-cooridante p1_x */
p1_x:
  .word 0x1a11808b
  .word 0x02e3d5a9
  .word 0x440d8db6
  .word 0x5ef02be3
  .word 0x2a35de10
  .word 0xdbdb132e
  .word 0xf84e7899
  .word 0x7dff4c2b
  .word 0x24705317
  .word 0x30eda4ab
  .word 0xb44ba799
  .word 0x3af8f1c5
  .zero 16

/* point 1 y-cooridante p1_y*/
p1_y:
  .word 0xa9f8b96e
  .word 0x82f268be
  .word 0x8e51c662
  .word 0x92b9c4bb
  .word 0x757d4493
  .word 0x26b4d3c6
  .word 0xf491007e
  .word 0x92a5c72a
  .word 0x8d8d8641
  .word 0x87498a20
  .word 0x0fe7dbde
  .word 0x841e4949
  .zero 16

/* scalar k */
scalar:
  .word 0xe8791ba3
  .word 0xf549e1f7
  .word 0x893be358
  .word 0x100794fe
  .word 0xbc9db95d
  .word 0xfd7ed624
  .word 0xc60ebab6
  .word 0x97ba9586
  .word 0xa026b431
  .word 0x37112316
  .word 0x8b26eef1
  .word 0xc1a0cf66
  .zero 16

   /* blinding parameter rnd */
 blinding_param:
  .word 0xa82c85b0
  .word 0x163ce1c8
  .word 0x32518fd7
  .word 0xf8a428cd
  .word 0xf5b9d867
  .word 0x00906f5f
  .word 0x7387b4f2
  .word 0xa2d3da7a
  .word 0xebe0a647
  .word 0xfb2ef7ca
  .word 0x74249432
  .word 0x230e5ff6
  .zero 16


/* Expected values in wide register file (x- and y-coordinates of result):
   [w1, w0] is affine x-coordinate of resulting point,
   [w3, w2] is affine y-coordinate of resulting point.
 w0  = 0x6c5d59dbafa8ecbaf0b2d3c1e818325403634e3b86956e6ead6739217b702c4a
 w1  = 0x00000000000000000000000000000000d177aa22a7c535a28cae00d420c4cd27
 w2  = 0x607c6c698fc5c15cbfadf94e322fa2fa5ff6cf915fe9ad62f538701f1add78ec
 w3  = 0x000000000000000000000000000000009e18fa893348fb1d44f40dbedcb5e36c
*/
