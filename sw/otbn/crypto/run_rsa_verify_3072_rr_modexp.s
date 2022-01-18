/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.section .text.start

/**
 * Standalone embeddable wrapper for 3072 bit RSA signature verification.
 *
 * Computes msg = (sig^65537) mod M, where
 *          sig is the signature
 *          M is the public key modulus
 *
 * Uses the OTBN RSA 3072-bit only modular exponentiation implementation to
 * obtain the message (digest) from an input signature. Assumes that the
 * Montgomery constant m0_inv is provided, but computes the RR constant on the
 * fly.
 *
 * The only exponent supported is e=65537.
 *
 * @param[in] dmem[in_mod]: Modulus of the RSA public key
 * @param[in] dmem[in_buf]: Signature to check against
 * @param[in] dmem[m0inv]: Montgomery constant (-(M^-1)) mod 2^256
 * @param[out] dmem[out_buf]: Recovered message digest
 */
run_rsa_verify_3072:

  /* Compute R^2 (same for both exponents): dmem[rr] <= R^2 */
  jal      x1, compute_rr

  /* Set pointers to buffers for modexp. */
  la        x24, out_buf
  la        x16, in_mod
  la        x23, in_buf
  la        x26, rr
  la        x17, m0inv

  /* run modular exponentiation */
  jal      x1, modexp_var_3072_f4

  ecall

.bss

/* Modulus of RSA-3072 key */
.globl in_mod
.balign 32
in_mod:
.zero 384

/* Montgomery constant m0' */
.globl m0inv
.balign 32
m0inv:
.zero 32

/* Squared Mongomery Radix RR = (2^3072)^2 mod N */
.globl rr
.balign 32
rr:
.zero 384

/* signature */
.globl in_buf
.balign 32
in_buf:
.zero 384

/* Output buffer. */
.globl out_buf
.balign 32
out_buf:
.zero 384
