/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Test for an RSA keygen subroutine: modular inverse of F4.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4

  /* Load DMEM pointers. */
  la        x12, modulus
  la        x13, result
  la        x14, tmp1
  la        x15, tmp2

  /* Load required constants. */
  li        x20, 20
  li        x21, 21

  /* Compute the modular inverse.
       dmem[result] <= (65537^-1) mod dmem[modulus] */
  jal       x1, modinv_f4

  /* Read the inverse into registers for the test framework to check.
       [w0..w3] <= dmem[result] */
  li        x2, 0
  loop      x30, 2
    bn.lid    x2, 0(x13++)
    addi      x2, x2, 1

  ecall

.data

/*
Modulus: randomly-generated even number in the range [2^1023,2^1024) such that
GCD(65537, modulus) = 1.

Python script to generate modulus:
import random
import math
while True:
  m = random.randrange(1 << 1022, 1 << 1023)
  m <<= 1
  if math.gcd(m, 65537) == 1:
    break

Full hex value for reference:
0x90800d989b5e0aae64b49cd617492911368b9ea8b791fcfe486c1313f039c66d0d6269927d1d7fe8454a24e8c9485587e7034021b6eebc5baced24ecef2a7e1d2bddada7ca3f234df00d25f25f281cbe2e5d51f0fe27f0c79b8823851f8011d89ebbcb1c2c3b3026830818fcd810c058fd74af138b61326b4775b51e0f4d68ea
*/
.balign 32
modulus:
.word 0x0f4d68ea
.word 0x4775b51e
.word 0x8b61326b
.word 0xfd74af13
.word 0xd810c058
.word 0x830818fc
.word 0x2c3b3026
.word 0x9ebbcb1c
.word 0x1f8011d8
.word 0x9b882385
.word 0xfe27f0c7
.word 0x2e5d51f0
.word 0x5f281cbe
.word 0xf00d25f2
.word 0xca3f234d
.word 0x2bddada7
.word 0xef2a7e1d
.word 0xaced24ec
.word 0xb6eebc5b
.word 0xe7034021
.word 0xc9485587
.word 0x454a24e8
.word 0x7d1d7fe8
.word 0x0d626992
.word 0xf039c66d
.word 0x486c1313
.word 0xb791fcfe
.word 0x368b9ea8
.word 0x17492911
.word 0x64b49cd6
.word 0x9b5e0aae
.word 0x90800d98

/* Buffer for result (1024 bits). */
.balign 32
result:
.zero 128

/* Working buffer (1024 bits). */
.balign 32
tmp1:
.zero 128

/* Working buffer (1024 bits). */
.balign 32
tmp2:
.zero 128
