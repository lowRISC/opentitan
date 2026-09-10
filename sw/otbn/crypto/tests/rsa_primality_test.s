/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Verify that a prime number passes the primality tests. */

.section .text.start

main:
  bn.xor    w31, w31, w31

  /* The number of limbs in this test. */
  li x30, 2

  /* Execute the Fermat test and store the result in an unused DMEM location. */
  jal x1, fermat_test
  la x3, mr_iter_p_tmp
  sw x2, 0(x3)

  /* Execute the Miller-Rabin test and store the result in an unused DMEM
     location. */
  jal x1, miller_rabin_test
  la x3, mr_iter_q_tmp
  sw x2, 0(x3)

  ecall
