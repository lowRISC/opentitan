/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * DMEM layout for the `run_rsa_modexp` OTBN app.
 */

.bss

/* RSA modulus (n), up to 4096 bits. */
.globl rsa_n
.balign 32
rsa_n:
.zero 512

# Enc/Sign: First private exponent share (d) up to 4096 bits.
# Keygen: Temp storage for rsa_p and second exponent share for primality tests.
.globl rsa_d0, rsa_p
.balign 32
/*----------------+----------+----------*
 |                |          |          |
 |      256B      |    d0    |          |
 |                |          |          |
 +----------------+----------+    d0    |
 |                |          |          |
 |      256B      |  rsa_p   |          |
 |                |          |          |
 *----------------+----------+----------*/
rsa_d0:
.zero 256
rsa_p:
.zero 256

# Enc/Sign: Second private exponent share (d) for signing, up to 4096 bits.
# Keygen: Temp storage for rsa_q and second exponent share for primality tests.
.globl rsa_d1, rsa_q
.balign 32
/*----------------+----------+----------*
 |                |          |          |
 |      256B      |    d1    |          |
 |                |          |          |
 +----------------+----------+    d1    |
 |                |          |          |
 |      256B      |  rsa_q   |          |
 |                |          |          |
 *----------------+----------+----------*/
rsa_d1:
.zero 256
rsa_q:
.zero 256

# r0, r1, r2 are the primary three 4096-bit computation regision for `modexp`.
.balign 32
.globl r0
.globl inout
r0:
inout:
.zero 512

.globl r1, mode, rsa_g
.balign 32
/*----------------+----------+----------*
 |                |    r1    |          |
 |      256B      |  (mode)  |          |
 |                |          |          |
 +----------------+----------+    r1    |
 |                |          |          |
 |      256B      |  rsa_g   |          |
 |                |          |          |
 *----------------+----------+----------*/
r1:
mode:
.zero 256
rsa_g:
.zero 256

.globl r2, rsa_h
.balign 32
/*----------------+----------+----------*
 |                |          |          |
 |      256B      |    r2    |          |
 |                |          |          |
 +----------------+----------+    r2    |
 |                |          |          |
 |      256B      |  rsa_h   |          |
 |                |          |          |
 *----------------+----------+----------*/
r2:
.zero 256
rsa_h:
.zero 256

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
