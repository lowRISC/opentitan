/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * DMEM layout for the `run_rsa_modexp` OTBN app.
 */

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

/* RSA first private exponent share (d) for signing, up to 4096 bits. */
.globl d0
.balign 32
d0:
.zero 512

/* RSA second private exponent share (d) for signing, up to 4096 bits. */
.globl d1
.balign 32
d1:
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

.section .scratchpad

/* Montgomery constant RR. Filled by `modload`. */
.balign 32
.globl RR
RR:
.zero 512

/* Scratchpad working buffer. */
.balign 32
.globl work_buf, buf0, buf1, buf2, buf3, buf4, buf5, buf6, buf7
work_buf:
buf0:
.zero 64
buf1:
.zero 64
buf2:
.zero 64
buf3:
.zero 64
buf4:
.zero 64
buf5:
.zero 64
buf6:
.zero 64
buf7:
.zero 64
