/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Standalone test to check an RSA keygen subroutine.
 *
 * The `relprime_small_primes` subroutine checks if a candidate prime is a
 * multiple of a small prime. This test ensures that the check detects a
 * multiple of 17.
 */

.section .text.start

main:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Load the number of limbs for this test. */
  li        x30, 4

  /* w22 <= 0 if dmem[simple_positive_input] is NOT relatively prime to F4 */
  la        x16, input
  jal       x1, relprime_small_primes

  ecall

.data

/**
 * A 1024-bit value that is a multiple of 17 and NOT 3 or 5.
 *
 * Full value for reference =
 * 0xfbe7d1a3a6642d2eb873e0b4c23eda03f9d299d8b5cbd03e735f18989c2f3e275e1d38306b2de24f70253a17b1197785e775bfbd717249031f4258944965eb3ff3078793cbff7898739b0062121017b7a328b77eddc338ec653f324f08771703909453a99c976fdc385d405480f795117ee9807fbe51cbe4b96770fb961719ba
 */
.balign 32
input:
.word 0x961719ba
.word 0xb96770fb
.word 0xbe51cbe4
.word 0x7ee9807f
.word 0x80f79511
.word 0x385d4054
.word 0x9c976fdc
.word 0x909453a9
.word 0x08771703
.word 0x653f324f
.word 0xddc338ec
.word 0xa328b77e
.word 0x121017b7
.word 0x739b0062
.word 0xcbff7898
.word 0xf3078793
.word 0x4965eb3f
.word 0x1f425894
.word 0x71724903
.word 0xe775bfbd
.word 0xb1197785
.word 0x70253a17
.word 0x6b2de24f
.word 0x5e1d3830
.word 0x9c2f3e27
.word 0x735f1898
.word 0xb5cbd03e
.word 0xf9d299d8
.word 0xc23eda03
.word 0xb873e0b4
.word 0xa6642d2e
.word 0xfbe7d1a3
