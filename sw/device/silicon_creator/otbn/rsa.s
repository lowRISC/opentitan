/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text
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


/**
 * RSA encryption
 */
rsa_encrypt:
  jal      x1, modload
  jal      x1, modexp_65537
  ecall

/**
 * RSA decryption
 */
rsa_decrypt:
  jal      x1, modload
  jal      x1, modexp
  ecall


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
  .word in

/* pointer to exponent buffer (dptr_exp, unused for encrypt) */
dptr_exp:
  .word exp

/* pointer to out buffer (dptr_out) */
dptr_out:
  .word out


/* Freely available DMEM space. */

m0d:
  /* filled by modload */
  .zero 512

RR:
  /* filled by modload */
  .zero 512

/* Modulus (n) */
.globl modulus
modulus:
  .zero 512

/* private exponent (d) */
.globl exp
exp:
  .zero 512

/* input data */
.globl in
in:
  .zero 512

/* output data */
.globl out
out:
  .zero 512
