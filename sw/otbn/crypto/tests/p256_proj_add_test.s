/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test for P-256 point addition in projective space
 *
 * Performs addition of two valid P-256 points in projective space.
 * Constant coordinates for the two points contained in the .data section.
 *
 * See comment at the end of the file for expected values of coordinates
 * of resulting point.
 */

.section .text.start

p256_proj_add_test:

  /* load curve points to w8..w13 */
  li       x2, 8
  la       x3, p1_x
  bn.lid   x2++, 0(x3)
  la       x3, p1_y
  bn.lid   x2++, 0(x3)
  la       x3, p1_z
  bn.lid   x2++, 0(x3)
  la       x3, p2_x
  bn.lid   x2++, 0(x3)
  la       x3, p2_y
  bn.lid   x2++, 0(x3)
  la       x3, p2_z
  bn.lid   x2++, 0(x3)
  
  /* load domain parameter b from dmem
     w30 <= a = dmem[p256_a] */
  li        x2, 30
  la        x3, p256_a
  bn.lid    x2, 0(x3)

  /* load domain parameter b from dmem
     w27 <= b = dmem[p256_b] */
  li        x2, 27
  la        x3, p256_b
  bn.lid    x2, 0(x3)

  /* load lower 256 bit of Barrett constant u for modulus p from dmem
     w28 <= u = dmem[p256_u_p] */
  li        x2, 28
  la        x3, p256_u_p
  bn.lid    x2, 0(x3)

  /* load field modulus p from dmem
     w29 <= p = dmem[p256_p] */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)

  /* store modulus to MOD WSR */
  bn.wsrw   0, w29

  /* init all-zero reg */
  bn.xor   w31, w31, w31

  jal      x1, proj_add

  ecall


.data

/* point 1 x-coordinate p1_x */
p1_x:
  .word 0x00000323
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 1 y-coordinate p1_y */
p1_y:
  .word 0x00000626
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 1 z-coordinate p1_z */
p1_z:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 2 x-coordinate p2_x */
p2_x:
  .word 0x00000346
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 2 y-coordinate p2_y */
p2_y:
  .word 0x00000643
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000

/* point 2 z-coordinate p2_z */
p2_z:
  .word 0x00000001
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
