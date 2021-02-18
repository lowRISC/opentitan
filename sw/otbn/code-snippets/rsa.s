/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text

 .globl rsa_encrypt
rsa_encrypt:
  jal      x1, modload
  jal      x1, modexp_65537
  ecall

/**
 * RSA decryption
 */
.globl rsa_decrypt
rsa_decrypt:
  jal      x1, modload
  jal      x1, modexp
  ecall


.data

/*
The structure of the 256b below are mandated by the calling convention of the
RSA library.
*/

/* reserved */
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
