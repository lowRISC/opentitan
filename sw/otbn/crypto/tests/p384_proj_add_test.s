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

.section .text.start

p384_proj_add_test:

  /* set dmem pointer to domain parameter b */
  la       x28, p384_b

  /* set dmem pointer to point 1 */
  la       x26, p1_x

  /* set dmem pointer to point 2 */
  la       x27, p2_x

  /* load domain parameter p (modulus)
     [w13, w12] = p */
  li       x2, 12
  la       x3, p384_p
  bn.lid   x2++, 0(x3)
  bn.lid   x2++, 32(x3)

  /* Compute Solinas constant k for modulus p (we know it is only 129 bits, so
     no need to compute the high part):
     w14 <= 2^256 - p[255:0] = (2^384 - p) mod (2^256) = 2^384 - p */
  bn.sub    w14, w31, w12

  /* init all-zero reg */
  bn.xor   w31, w31, w31

  /* set reg file pointers */
  li x22,  10
  li x23,  11
  li x24,  16
  li x25,  17

  jal      x1, proj_add_p384

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
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 2 y-cooridante p1_y */
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
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 1 z-cooridante p1_z */
p1_z:
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
p2_x:
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
p2_y:
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
p2_z:
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
