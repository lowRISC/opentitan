/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Embeddable binary that runs modular exponentiation for RSA.
 *
 * The caller must always supply an RSA modulus `n` and a base `a` for the
 * exponentiation (in practice, `a` is a message or a signature). Using the
 * `mode` parameter, the caller indicates the modulus size and selects either:
 *   (a) `modexp` mode: computes a^d mod n for a caller-provided exponent d
 *   (b) `modexp_f4` mode: computes a^65537 mod n
 *
 * In `modexp_f4` mode, the caller does not need to provide an exponent.
 *
 * The base `a` and exponent `d` (if provided) should be the same size as the
 * modulus; additional bits will be ignored.
 *
 * This binary can be used for either RSA signing or encryption.
 */

/**
 * Mode magic values generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 6 -n 11 \
 *      -s 544077332 --avoid-zero

 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_RSA_2048_MODEXP, 0x76b
.equ MODE_RSA_2048_MODEXP_F4, 0x565
.equ MODE_RSA_3072_MODEXP, 0x378
.equ MODE_RSA_3072_MODEXP_F4, 0x6d1
.equ MODE_RSA_4096_MODEXP, 0x70b
.equ MODE_RSA_4096_MODEXP_F4, 0x0ee

.section .text.start
start:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la      x2, mode
  lw      x2, 0(x2)

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

rsa_2048_modexp:
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
  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, n
  la    x17, m0d
  la    x18, RR

  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[work_buf] = dmem[inout]^dmem[d] mod dmem[n] */
  la       x14, inout
  la       x15, d
  la       x2, work_buf
  jal      x1, modexp

  /* Copy final result to the output buffer. */
  la    x3, work_buf
  la    x4, inout
  loop  x30, 2
    bn.lid x0, 0(x3++)
    bn.sid x0, 0(x4++)

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
  la    x16, n
  la    x17, m0d
  la    x18, RR

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

.bss

/* Operational mode. */
.globl mode
.balign 4
mode:
.zero 4

/* RSA modulus (n), up to 4096 bits. */
.globl n
.balign 32
n:
.zero 512

/* RSA private exponent (d) for signing, up to 4096 bits. */
.globl d
.balign 32
d:
.zero 512

/**
 * Buffer used for both input and output, up to 4096 bits.
 *
 * - Input: Base for exponentiation (a), e.g. message digest or signature.
 * - Output: Modular exponentiation result.
 */
.balign 32
.globl inout
inout:
.zero 512


/* Montgomery constant m0'. Filled by `modload`. */
/* Note: m0' could go in scratchpad if there was space. */
.balign 32
m0d:
.zero 32

.section .scratchpad

/* Montgomery constant RR. Filled by `modload`. */
.balign 32
RR:
.zero 512

/* Scratchpad working buffer. */
.balign 32
work_buf:
.zero 512
