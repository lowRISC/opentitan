/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   Standalone test for P-384 point addition in projective space
 *
 *   Performs addition of two valid P-384 points in projective space.
 *   Constant coordinates for the two points contained in the .data section.
 *
 *   See comment at the end of the file for expected values of coordinates
 *   of resulting point.
 */

.section .text

p384_scalar_mult_test:

  /* set dmem pointer to domain parameter b */
  lw       x28, 32(x0)

  /* set dmem pointer to point x-coordinate */
  lw       x20, 20(x0)

  /* set dmem pointer to point y-coordinate */
  lw       x21, 24(x0)

  /* set dmem pointer to scalar d */
  lw       x19, 28(x0)

  /* set dmem pointer to scratchpad */
  lw       x30, 60(x0)

  /* set pointer to blinding parameter */
  lw       x9, 4(x0)

  /* load domain parameter p (modulus)
     [w13, w12] = p = dmem[dptr_p] */
  li       x2, 12
  lw       x3, 36(x0)
  bn.lid   x2++, 0(x3)
  bn.lid   x2++, 32(x3)

  /* load Barrett constant u for modulus p
     [w15, w14] = u = dmem[dptr_u] */
  li       x2, 14
  lw       x3, 40(x0)
  bn.lid   x2++, 0(x3)
  bn.lid   x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = p = dmem[dptr_n] */
  li       x2, 10
  lw       x3, 44(x0)
  bn.lid   x2++, 0(x3)
  bn.lid   x2++, 32(x3)

  /* init all-zero reg */
  bn.xor   w31, w31, w31

  jal      x1, scalar_mult_int_p384

  ecall


.data

/* pointer to k (dptr_k) */
.word 0x00000000

/* pointer to rnd (dptr_rnd) */
.word 0x00000100

/* pointer to msg (dptr_msg) */
.word 0x00000000

/* pointer to R (dptr_r) */
.word 0x00000080

/* pointer to S (dptr_s) */
.word 0x00000000

/* pointer to X (dptr_x) */
.word 0x00000200

/* pointer to Y (dptr_y) */
.word 0x00000240

/* pointer to D (dptr_d) */
.word 0x00000280

/* pointer to b (dptr_b) */
.word 0x00000040

/* pointer to p (dptr_p) */
.word 0x00000080

/* pointer to u_p (dptr_u_p) */
.word 0x000000C0

/* pointer to n (dptr_n) */
.word 0x00000140

/* pointer to u_n (dptr_u_n) */
.word 0x00000180

/* pointer reserved */
.word 0x00000000

/* pointer reserved */
.word 0x00000000

/* pointer to scratchpad (dptr_sc) */
.word 0x00000400

/* P-384 domain parameter b */
.word 0xd3ec2aef
.word 0x2a85c8ed
.word 0x8a2ed19d
.word 0xc656398d
.word 0x5013875a
.word 0x0314088f
.word 0xfe814112
.word 0x181d9c6e
.word 0xe3f82d19
.word 0x988e056b
.word 0xe23ee7e4
.word 0xb3312fa7
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* P-384 domain parameter p (modulus) */
.word 0xffffffff
.word 0x00000000
.word 0x00000000
.word 0xffffffff
.word 0xfffffffe
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* barrett constant u for modulus p */
.word 0x00000001
.word 0xffffffff
.word 0xffffffff
.word 0x00000000
.word 0x00000001
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* blinding parameter rnd */
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
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* P-384 domain parameter n (order of base point) */
.word 0xccc52973
.word 0xecec196a
.word 0x48b0a77a
.word 0x581a0db2
.word 0xf4372ddf
.word 0xc7634d81
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0xffffffff
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* barrett constant u for n */
.word 0x333ad68d
.word 0x1313e695
.word 0xb74f5885
.word 0xa7e5f24d
.word 0x0bc8d220
.word 0x389cb27e
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

.skip 64

/* point 1 x-cooridante p1_x */
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
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* point 1 y-cooridante p1_y*/
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
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* scalar d */
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
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000


/* Expected values in wide register file (x-, y-, z-coordinates of result):
 w25 = 0xef7708f41bbd11f35b8e12b38f00a42fd36a61172d671c55af2fb83e5e2768b2
 w26 = 0x0000000000000000000000000000000039f74a9991901c41c97c172dac3ef8f6
 w27 = 0x723f7e531aaec58f79696d30ec5a9d8c4d27089be55405b1f463dd15bcb37ff3
 w28 = 0x000000000000000000000000000000004e10de4fed82598a6e7daefaf5a33ebd
 w29 = 0x294dec2a532367d83c66f87d33c58a3cd2ff538e0f548d4c3d90bf240e29d9a6
 w30 = 0x00000000000000000000000000000000d9c6373a4dc096ab3cb63dee1b672b21
 */
