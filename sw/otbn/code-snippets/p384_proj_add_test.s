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

p384_proj_add_test:

  /* set dmem pointer to domain parameter b */
  li       x28, 0

  /* set dmem pointer to point 1 */
  li       x26,  512

  /* set dmem pointer to point 2 */
  li       x27, 704

  /* load domain parameter p (modulus)
     [w1, w0] = p */
  li       x2, 12
  bn.lid   x2++,  64(x0)
  bn.lid   x2++,  96(x0)

  /* load Barrett constant u for modulus p
     [w15, w14] = p */
  li       x2, 14
  bn.lid   x2++,  128(x0)
  bn.lid   x2++,  160(x0)

  /* init all-zero reg */
  bn.xor   w31, w31, w31

  /* set reg file pointers */
  li x22,  10
  li x23,  11
  li x24,  16
  li x25,  17

  jal      x1, proj_add_p384

  ecall


.data

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

.skip 320

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

/* point 2 y-cooridante p1_y*/
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

/* point 1 z-cooridante p1_z*/
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
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* point 2 x-cooridante p2_x */
.word 0xa24055fe
.word 0x44e0b41c
.word 0xb747a4ee
.word 0xd5597d02
.word 0x56cd166d
.word 0xd147078b
.word 0x57f91304
.word 0x255b83b1
.word 0x33eabb2d
.word 0xf83f0a61
.word 0x3ff2df87
.word 0x77da1284
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* point 2 y-cooridante p2_y */
.word 0x8d803d57
.word 0x9ea243f3
.word 0xde9000a7
.word 0x35f5b65f
.word 0x417d5e7c
.word 0x21a9269f
.word 0x98a79201
.word 0xa9311cb0
.word 0x8047b439
.word 0xb7494b0d
.word 0x63d2f480
.word 0x699a7b9a
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* point 2 z-cooridante p2_z */
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
.word 0x00000000
.word 0x00000000
.word 0x00000000
.word 0x00000000

/* Expected values wide register file (x-, y-, z-coordinates of result):
 w25 = 0xb89ab3a5653144bbde19809f8c041d592417c47c798a1333a3dbd2e105e101e2
 w26 = 0x00000000000000000000000000000000103520c6699791fc8442cbea85ed03b4
 w27 = 0x4a2f5605fb42124188b528e5597a081a811cb37702220144ab04587d6f9c1521
 w28 = 0x00000000000000000000000000000000b29ca8ba3f6c2b82859bcf8046c5769b
 w29 = 0x2f9731e1883f5baa7d3d7cae88ff2d29d5ca5d208c94d4207bf986ff256d1217
 w30 = 0x000000000000000000000000000000005ffbcc52aae3707a63c630115c735f94
 */
