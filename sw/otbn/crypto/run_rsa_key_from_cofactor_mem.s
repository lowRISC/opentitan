/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * DMEM layout for the `run_rsa_keygen` OTBN app.
 */

.bss

/* RSA modulus n = p*q (up to 4096 bits). */
.balign 32
.globl rsa_n
rsa_n:
.zero 512

/*
 * RSA first Boolean share of the private exponent (d) for decryption and
 * signing, up to 4096 bits.
 */
.globl rsa_d0
.balign 32
rsa_d0:
.zero 512

/*
 * RSA second Boolean share of the private exponent (d) for decryption and
 * signing, up to 4096 bits.
 */
.globl rsa_d1
.balign 32
rsa_d1:
.zero 512

/* Prime cofactor for n for `rsa_key_from_cofactor`; also used as a temporary
 * work buffer. */
.balign 32
.globl rsa_cofactor
rsa_cofactor:
.zero 512

/* Montgomery constant R^2 (up to 2048 bits). */
.balign 32
.globl mont_rr
mont_rr:
.zero 256

/* Operational mode. */
.globl mode
.balign 4
mode:
.zero 4

.section .scratchpad

/* Extra label marking the start of p || q in memory. The `derive_d` function
   uses this to get a 512-byte working buffer, which means p and q must be
   continuous in memory. In addition, `rsa_key_from_cofactor` uses the
   larger buffer for division and depends on the order of `p` and `q`. */
.balign 32
.globl rsa_pq
rsa_pq:

/* Secret RSA `p` parameter (prime). Up to 2048 bits. */
.globl rsa_p
rsa_p:
.zero 256

/* Secret RSA `q` parameter (prime). Up to 2048 bits. */
.globl rsa_q
rsa_q:
.zero 256

/* Temporary working buffer (4096 bits). */
.balign 32
.globl tmp_scratchpad, tmp0, tmp1, tmp2, tmp3, tmp4, tmp5, tmp6, tmp7
tmp_scratchpad:
tmp0:
.zero 64
tmp1:
.zero 64
tmp2:
.zero 64
tmp3:
.zero 64
tmp4:
.zero 64
tmp5:
.zero 64
tmp6:
.zero 64
tmp7:
.zero 64
