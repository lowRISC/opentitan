/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

main:
  /* Initialize all-zero register. */
  bn.xor    w31, w31, w31

  /* Number of limbs (n) and related constant.
       x30 <= n
       x31 <= n - 1 */
  li        x30, 2
  li        x31, 1

  la       x23, r0
  la       x24, r1
  la       x25, r2
  la       x26, d0
  la       x27, d1
  la       x28, n
  la       x29, RR
  jal      x1, check_primality

  ecall
