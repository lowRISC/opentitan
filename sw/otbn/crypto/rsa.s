/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
.globl start
start:
  /* Init all-zero register. */
  bn.xor  w31, w31, w31

  /* Load number of limbs. */
  la    x2, n_limbs
  lw    x30, 0(x2)

  /* Load pointers to modulus and Montgomery constant buffers. */
  la    x16, modulus
  la    x17, m0d
  la    x18, RR

  /* Read mode, then tail-call either rsa_encrypt or rsa_decrypt */
  la    x2, mode
  lw    x2, 0(x2)

  li    x3, 1
  beq   x2, x3, rsa_encrypt

  li    x3, 2
  beq   x2, x3, rsa_decrypt

  /* Mode is neither 1 (= encrypt) nor 2 (= decrypt). Fail. */
  unimp

.text

/**
 * RSA encryption
 */
rsa_encrypt:
  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[work_buf] = dmem[inout]^65537 mod dmem[modulus] */
  la       x14, inout
  la       x2, work_buf
  jal      x1, modexp_65537

  /* dmem[inout] <= dmem[work_buf] */
  jal      x1, cp_work_buf
  ecall

/**
 * RSA decryption
 */
rsa_decrypt:
  /* Compute Montgomery constants. */
  jal      x1, modload

  /* Run exponentiation.
       dmem[work_buf] = dmem[inout]^dmem[exp] mod dmem[modulus] */
  la       x14, inout
  la       x15, exp
  la       x2, work_buf
  jal      x1, modexp

  /* dmem[inout] <= dmem[work_buf] */
  jal      x1, cp_work_buf
  ecall

/**
 * Zero the contents of work_buf
 *
 * clobbered registers: x3, w0
 */
zero_work_buf:
  la     x3, work_buf
  bn.xor w0, w0, w0
  /* The buffer is 512 bytes long, which needs sixteen 256b words. */
  loopi 16, 1
    bn.sid x0, 0(x3++)
  ret

/**
 * Copy the contents of work_buf onto inout
 *
 * clobbered registers: x2, x3, x4, w0
 */
cp_work_buf:
  la    x2, n_limbs
  lw    x30, 0(x2)
  la    x3, work_buf
  la    x4, inout
  loop  x30, 2
    bn.lid x0, 0(x3++)
    bn.sid x0, 0(x4++)
  ret

.bss

/* Mode (1 = encrypt; 2 = decrypt) */
.globl mode
mode:
  .word 0x00000000

/* N: Key/modulus size in 256b limbs (i.e. for RSA-1024: N = 4) */
.globl n_limbs
n_limbs:
  .word 0x00000000

/* Modulus (n) */
.balign 32
.globl modulus
modulus:
  .zero 512

/* private exponent (d) */
.balign 32
.globl exp
exp:
  .zero 512

/* input/output data */
.balign 32
.globl inout
inout:
  .zero 512

/* Montgomery constant m0'. Filled by `modload`. */
.balign 32
m0d:
  /* could go in scratchpad if there was space */
  .zero 32

.section .scratchpad

/* Montgomery constant RR. Filled by `modload`. */
.balign 32
RR:
  .zero 512

/* working data */
.balign 32
work_buf:
  .zero 512
