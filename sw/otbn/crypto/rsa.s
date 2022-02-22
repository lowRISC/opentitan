/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start
.globl start
start:
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
  jal      x1, zero_work_buf
  jal      x1, modload
  jal      x1, modexp_65537
  jal      x1, cp_work_buf
  ecall

/**
 * RSA decryption
 */
rsa_decrypt:
  jal      x1, zero_work_buf
  jal      x1, modload
  jal      x1, modexp
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
  /* The buffer is 480 bytes long, which needs fourteen 256b words. */
  loopi 14, 1
    bn.sid x0, 0(x3++)
  ret

/**
 * Copy the contents of work_buf onto inout
 *
 * clobbered registers: x3, x4, w0
 */
cp_work_buf:
  la  x3, work_buf
  la  x4, inout
  /* The buffers are 480 bytes long, which we can load/store with
     fourteen 256b words. */
  loopi 14, 2
    bn.lid x0, 0(x3++)
    bn.sid x0, 0(x4++)
  ret

.data
/*
The structure of the 256b below are mandated by the calling convention of the
RSA library.
*/

/* Mode (1 = encrypt; 2 = decrypt) */
.globl mode
mode:
  .word 0x00000000

/* N: Key/modulus size in 256b limbs (i.e. for RSA-1024: N = 4) */
.globl n_limbs
n_limbs:
  .word 0x00000000

/* pointer to m0' (dptr_m0d) */
dptr_m0d:
  .word m0d

/* pointer to RR (dptr_rr) */
dptr_rr:
  .word RR

/* load pointer to modulus (dptr_m) */
dptr_m:
  .word modulus

/* pointer to base bignum buffer (dptr_in) */
dptr_in:
  .word inout

/* pointer to exponent buffer (dptr_exp, unused for encrypt) */
dptr_exp:
  .word exp

/* pointer to out buffer (dptr_out) */
dptr_out:
  .word work_buf

/* (End of fixed-layout section) */


/* Modulus (n) */
.globl modulus
modulus:
  .zero 512

/* private exponent (d) */
.globl exp
exp:
  .zero 512

/* input/output data */
.globl inout
inout:
  .zero 512


.section .scratchpad
m0d:
  /* filled by modload */
  .zero 32

RR:
  /* filled by modload */
  .zero 512

/* working data */
work_buf:
  .zero 480
