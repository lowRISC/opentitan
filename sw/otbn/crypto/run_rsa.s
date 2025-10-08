/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Embeddable binary that runs RSA encryption/decryption, sign/verify and
 * key generation for various moduli sizes.
 */

/**
 * Mode magic values generated with
 * $ ./util/design/sparse-fsm-encode.py -d 4 -m 14 -n 11 \
 *    -s 347912204 --avoid-zero
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */

# Key generation modes

# Testing only! These key lengths are not supported by the cryptolib.
.equ MODE_RSA_1024_KEYGEN, 0x528
# Supported key lengths.
.equ MODE_RSA_2048_KEYGEN, 0x799
.equ MODE_RSA_3072_KEYGEN, 0x4e0
.equ MODE_RSA_4096_KEYGEN, 0x3ca

# Encryption/Signature modes

# Testing only! These key lengths are not supported by the cryptolib.
.equ MODE_RSA_512_MODEXP,     0x3ad
.equ MODE_RSA_512_MODEXP_F4,  0x37f
.equ MODE_RSA_1024_MODEXP,    0x65c
.equ MODE_RSA_1024_MODEXP_F4, 0x50f
# Supported key lengths.
.equ MODE_RSA_2048_MODEXP,    0x582
.equ MODE_RSA_2048_MODEXP_F4, 0x095
.equ MODE_RSA_3072_MODEXP,    0x20e
.equ MODE_RSA_3072_MODEXP_F4, 0x1be
.equ MODE_RSA_4096_MODEXP,    0x361
.equ MODE_RSA_4096_MODEXP_F4, 0x3d4

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_RSA_1024_KEYGEN
.globl MODE_RSA_2048_KEYGEN
.globl MODE_RSA_3072_KEYGEN
.globl MODE_RSA_4096_KEYGEN
.globl MODE_RSA_512_MODEXP
.globl MODE_RSA_512_MODEXP_F4
.globl MODE_RSA_1024_MODEXP
.globl MODE_RSA_1024_MODEXP_F4
.globl MODE_RSA_2048_MODEXP
.globl MODE_RSA_2048_MODEXP_F4
.globl MODE_RSA_3072_MODEXP
.globl MODE_RSA_3072_MODEXP_F4
.globl MODE_RSA_4096_MODEXP
.globl MODE_RSA_4096_MODEXP_F4

.section .text.start
start:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la      x2, mode
  lw      x2, 0(x2)

  add     x3, x0, MODE_RSA_1024_KEYGEN
  beq     x2, x3, rsa_1024_keygen

  add     x3, x0, MODE_RSA_2048_KEYGEN
  beq     x2, x3, rsa_2048_keygen

  add     x3, x0, MODE_RSA_3072_KEYGEN
  beq     x2, x3, rsa_3072_keygen

  add     x3, x0, MODE_RSA_4096_KEYGEN
  beq     x2, x3, rsa_4096_keygen

  addi    x3, x0, MODE_RSA_512_MODEXP
  beq     x2, x3, rsa_512_modexp

  addi    x3, x0, MODE_RSA_512_MODEXP_F4
  beq     x2, x3, rsa_512_modexp_f4

  addi    x3, x0, MODE_RSA_1024_MODEXP
  beq     x2, x3, rsa_1024_modexp

  addi    x3, x0, MODE_RSA_1024_MODEXP_F4
  beq     x2, x3, rsa_1024_modexp_f4

  addi    x3, x0, MODE_RSA_2048_MODEXP
  beq     x2, x3, rsa_2048_modexp

  addi    x3, x0, MODE_RSA_2048_MODEXP_F4
  beq     x2, x3, rsa_2048_modexp_f4

  addi    x3, x0, MODE_RSA_3072_MODEXP
  beq     x2, x3, rsa_3072_modexp

  addi    x3, x0, MODE_RSA_3072_MODEXP_F4
  beq     x2, x3, rsa_3072_modexp_f4

  addi    x3, x0, MODE_RSA_4096_MODEXP
  beq     x2, x3, rsa_4096_modexp

  addi    x3, x0, MODE_RSA_4096_MODEXP_F4
  beq     x2, x3, rsa_4096_modexp_f4

  /* Unsupported mode; fail. */
  unimp
  unimp
  unimp

rsa_1024_keygen:
  /* Set the number of limbs for the modulus (1024 / 256 = 4). */
  li      x30, 4

  /* Tail-call keygen. */
  jal     x0, do_keygen

rsa_2048_keygen:
  /* Set the number of limbs for the modulus (2048 / 256 = 8). */
  li      x30, 8

  /* Tail-call keygen. */
  jal     x0, do_keygen

rsa_3072_keygen:
  /* Set the number of limbs for the modulus (3072 / 256 = 12). */
  li      x30, 12

  /* Tail-call keygen. */
  jal     x0, do_keygen

rsa_4096_keygen:
  /* Set the number of limbs for the modulus (4096 / 256 = 16). */
  li      x30, 16

  /* Tail-call keygen. */
  jal     x0, do_keygen

rsa_512_modexp:
  /* Enable message blinding. */
  li x29, 1

  /* Set the number of limbs for the modulus (512 / 256 = 2). */
  li      x30, 2

  /* Tail-call modexp. */
  jal     x0, do_modexp

rsa_512_modexp_f4:
  /* Set the number of limbs for the modulus (512 / 256 = 2). */
  li      x30, 2

  /* Tail-call modexp_f4. */
  jal     x0, do_modexp_f4

rsa_1024_modexp:
  /* Enable message blinding. */
  li x29, 1

  /* Set the number of limbs for the modulus (1024 / 256 = 4). */
  li      x30, 4

  /* Tail-call modexp. */
  jal     x0, do_modexp

rsa_1024_modexp_f4:
  /* Set the number of limbs for the modulus (1024 / 256 = 4). */
  li      x30, 4

  /* Tail-call modexp_f4. */
  jal     x0, do_modexp_f4

rsa_2048_modexp:
  /* Enable message blinding. */
  li x29, 1

  /* Set the number of limbs for the modulus (2048 / 256 = 8). */
  li      x30, 8

  /* Tail-call modexp. */
  jal     x0, do_modexp

rsa_2048_modexp_f4:
  /* Set the number of limbs for the modulus (2048 / 256 = 8). */
  li      x30, 8

  /* Tail-call modexp_f4. */
  jal     x0, do_modexp_f4

rsa_3072_modexp:
  /* Enable message blinding. */
  li x29, 1

  /* Set the number of limbs for the modulus (3072 / 256 = 12). */
  li      x30, 12

  /* Tail-call modexp. */
  jal     x0, do_modexp

rsa_3072_modexp_f4:
  /* Set the number of limbs for the modulus (3072 / 256 = 12). */
  li      x30, 12

  /* Tail-call modexp_f4. */
  jal     x0, do_modexp_f4

rsa_4096_modexp:
  /* Enable message blinding. */
  li x29, 1

  /* Set the number of limbs for the modulus (4096 / 256 = 16). */
  li      x30, 16

  /* Tail-call modexp. */
  jal     x0, do_modexp

rsa_4096_modexp_f4:
  /* Set the number of limbs for the modulus (4096 / 256 = 16). */
  li      x30, 16

  /* Tail-call modexp_f4. */
  jal     x0, do_modexp_f4

/**
 * Invoke the RSA key generation algorithm.
 *
 * Calls `ecall` when done; should be tail-called by mode-specific routines
 * after the number of limbs is set.
 *
 * @param[in] x30: number of limbs for modulus
 * @param[out] dmem[n]: n, modulus
 * @param[out] dmem[d0]: d0, first share of secret exponent
 * @param[out] dmem[d1]: d1, second share of secret exponent
 */
do_keygen:
  # Save mode indicator in register.
  la x16, mode
  lw x28, 0(x16)

  jal x1, rsa_keygen

  # Restore mode indicator in DMEM.
  la x16, mode
  sw x28, 0(x16)

  ecall

/**
 * Precompute constants and call modular exponentiation.
 *
 * Calls `ecall` when done; should be tail-called by mode-specific routines
 * after the number of limbs is set.
 *
 * @param[in]          x30: number of limbs for modulus
 * @param[in]      dmem[n]: n, modulus
 * @param[in]      dmem[d]: d, exponent
 * @param[in]  dmem[inout]: a, base for exponentiation
 * @param[out] dmem[inout]: result, a^d mod n
 */
do_modexp:
  # Save mode indicator in register.
  la x16, mode
  lw x28, 0(x16)

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, rsa_n
  la    x17, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[inout] = dmem[inout]^dmem[d] mod dmem[n] */
  jal      x1, modexp

  # Restore mode indicator in DMEM.
  la x16, mode
  sw x28, 0(x16)

  ecall

/**
 * Precompute constants and call modular exponentiation.
 *
 * Calls `ecall` when done; should be tail-called by mode-specific routines
 * after the number of limbs is set.
 *
 * @param[in]          x30: number of limbs for modulus
 * @param[in]      dmem[n]: n, modulus
 * @param[in]  dmem[inout]: a, base for exponentiation
 * @param[out] dmem[inout]: result, a^65537 mod n
 */
do_modexp_f4:
  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, rsa_n
  la    x17, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[work_buf] = dmem[inout]^65537 mod dmem[n] */
  la       x14, inout
  la       x2, work_buf
  jal      x1, modexp_65537

  /* Copy final result to the output buffer. */
  la    x3, work_buf
  la    x4, inout
  loop  x30, 2
    bn.lid x0, 0(x3++)
    bn.sid x0, 0(x4++)

  ecall
