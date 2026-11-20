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

# Enc/Sign: First and second private exponent shares (d0, d1) up to 4096 bits.
# Keygen: Temp storage for rsa_g and rsa_h during primality tests, and a
# contiguous (n + 1)-limb working buffer (rsa_d, up to 544B) for `modinv_f4`
# before d is split into Boolean shares d0 and d1.
.globl rsa_d, rsa_d0, rsa_g, rsa_d1, rsa_h
.balign 32
/*----------------+----------+----------*
 |                |          |          |
 |      256B      |    d0    |          |
 |                |          |    d0    |
 +----------------+----------+          |
 |                |          |          |
 |      256B      |  rsa_g   |          |
 |                |          |  (rsa_d) |
 +----------------+----------+          |
 |                |          |          |
 |      256B      |    d1    |          |
 |                |          |    d1    |
 +----------------+----------+          |
 |                |          |          |
 |      256B      |  rsa_h   |          |
 |                |          |          |
 *----------------+----------+----------*/
rsa_d:
rsa_d0:
.zero 256
rsa_g:
.zero 256
rsa_d1:
.zero 256
rsa_h:
.zero 256

# r0, r1, r2 are the primary three 4096-bit computation regision for `modexp`.
.balign 32
.globl r0
.globl inout
r0:
inout:
.zero 512

.globl r1, mode, ok, rsa_e, rsa_p
.balign 32
/*----------------+----------+----------*
 |                |    r1    |          |
 |      256B      |  (mode)  |          |
 |                |   (ok)   |          |
 |                |  (rsa_e) |          |
 +----------------+----------+    r1    |
 |                |          |          |
 |      256B      |  rsa_p   |          |
 |                |          |          |
 *----------------+----------+----------*/
r1:
mode:
.zero 4
ok:
.zero 4
rsa_e:
.zero 4
/* 244 bytes of padding */
.zero 244
rsa_p:
.zero 256

.globl r2, rsa_q, mr_iter_p, mr_iter_q
.balign 32
/*----------------+----------+----------*
 |                |          |          |
 |      256B      |    r2    |          |
 |                |          |          |
 +----------------+----------+    r2    |
 |                |          |          |
 |      256B      |  rsa_q   |          |
 |                |          |          |
 *----------------+----------+----------*/
r2:
mr_iter_p:
.zero 4
mr_iter_q:
.zero 4
.zero 248
rsa_q:
.zero 256

.section .scratchpad

/* Montgomery constant RR. Filled by `modload`. */
.balign 32
.globl RR
RR:
.zero 512

/* Scratchpad working buffer (512B).
 * During 4096-bit modexp, all 512B of `work_buf` are used while the keygen
 * temporaries in the upper 64B are inactive. During keygen, `work_buf_kgen`
 * uses at most 10 limbs (320B) and `modexp` uses at most 8 limbs (256B),
 * leaving the upper 64B free for temporaries. */
.balign 32
.globl work_buf, work_buf_kgen, nlimbs_tmp, mode_tmp, mr_iter_p_tmp, mr_iter_q_tmp
.globl fi_save_x26, fi_save_x27, fi_save_x28
/*----------------*----------------*----------*
 |                |                |          |
 |      448B      |  work_buf_kgen |          |
 |                |                |          |
 +----------------+----------------+ work_buf |
 |                |  (nlimbs_tmp)  |          |
 |                | (mr_iter_*_tmp)|          |
 |       64B      | (fi_save_x26..)|          |
 |                |   (mode_tmp)   |          |
 *----------------*----------------*----------*/
work_buf:
work_buf_kgen:
.zero 448
nlimbs_tmp:
.zero 4
mr_iter_p_tmp:
.zero 4
mr_iter_q_tmp:
.zero 4
fi_save_x26:
.zero 4
fi_save_x27:
.zero 4
fi_save_x28:
.zero 4
.zero 36
mode_tmp:
.zero 4
