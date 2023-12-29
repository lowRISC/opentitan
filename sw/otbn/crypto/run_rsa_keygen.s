/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * RSA key generation.
 *
 * This binary can be called in two different modes:
 * - `GEN` mode generates a new, random keypair
 * - `COFACTOR` mode constructs a keypair from n, e, d, and either p or q.
 *
 * Both modes support three sizes: RSA-2048, RSA-3072, and RSA-4096.
 */

/**
 * Mode magic values generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 6 -n 11 \
 *    --avoid-zero -s 561689407
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_GEN_RSA_2048, 0x137
.equ MODE_GEN_RSA_3072, 0x4e5
.equ MODE_GEN_RSA_4096, 0x63a
.equ MODE_COFACTOR_RSA_2048, 0x34e
.equ MODE_COFACTOR_RSA_3072, 0x0db
.equ MODE_COFACTOR_RSA_4096, 0x794

.section .text.start
start:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la      x2, mode
  lw      x2, 0(x2)

  addi    x3, x0, MODE_GEN_RSA_2048
  beq     x2, x3, rsa_keygen_2048

  addi    x3, x0, MODE_GEN_RSA_3072
  beq     x2, x3, rsa_keygen_3072

  addi    x3, x0, MODE_GEN_RSA_4096
  beq     x2, x3, rsa_keygen_4096

  addi    x3, x0, MODE_COFACTOR_RSA_2048
  beq     x2, x3, rsa_key_from_cofactor_2048

  addi    x3, x0, MODE_COFACTOR_RSA_3072
  beq     x2, x3, rsa_key_from_cofactor_3072

  addi    x3, x0, MODE_COFACTOR_RSA_4096
  beq     x2, x3, rsa_key_from_cofactor_4096

  /* Unsupported mode; fail. */
  unimp
  unimp
  unimp

rsa_keygen_2048:
  /* Set the number of limbs for the primes (2048 / 2 / 256). */
  li      x30, 4

  /* Generate a key (results in dmem[rsa_n] and dmem[rsa_d]). */
  jal     x1, rsa_keygen
  ecall

rsa_keygen_3072:
  /* Set the number of limbs for the primes (3072 / 2 / 256). */
  li      x30, 6

  /* Generate a key (results in dmem[rsa_n] and dmem[rsa_d]). */
  jal     x1, rsa_keygen
  ecall

rsa_keygen_4096:
  /* Set the number of limbs for the primes (4096 / 2 / 256). */
  li      x30, 8

  /* Generate a key (results in dmem[rsa_n] and dmem[rsa_d]). */
  jal     x1, rsa_keygen
  ecall

rsa_key_from_cofactor_2048:
  /* Set the number of limbs for the primes (2048 / 2 / 256). */
  li      x30, 4

  /* Generate a key (results in dmem[rsa_n] and dmem[rsa_d]). */
  jal     x1, rsa_key_from_cofactor
  ecall

rsa_key_from_cofactor_3072:
  /* Set the number of limbs for the primes (3072 / 2 / 256). */
  li      x30, 6

  /* Generate a key (results in dmem[rsa_n] and dmem[rsa_d]). */
  jal     x1, rsa_key_from_cofactor
  ecall

rsa_key_from_cofactor_4096:
  /* Set the number of limbs for the primes (4096 / 2 / 256). */
  li      x30, 8

  /* Generate a key (results in dmem[rsa_n] and dmem[rsa_d]). */
  jal     x1, rsa_key_from_cofactor
  ecall

.bss

/* Operational mode. */
.globl mode
.balign 4
mode:
.zero 4
