/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * DMEM layout for the `p384` OTBN app.
 */

.bss

/* Operational mode. */
.globl mode
.balign 4
mode:
  .zero 4

/* Success code for basic validity checks on the public key and signature. */
.globl ok
.balign 4
ok:
  .zero 4

/* Message digest. */
.globl msg
.balign 32
msg:
  .zero 64

/* Signature R. */
.globl r
.balign 32
r:
  .zero 64

/* Signature S. */
.globl s
.balign 32
s:
  .zero 64

/* Public key x-coordinate. */
.globl x
.balign 32
x:
  .zero 64

/* Public key y-coordinate. */
.globl y
.balign 32
y:
  .zero 64

/* Private key input/output buffer. */
.globl d0_io
.balign 32
d0_io:
  .zero 64

.globl d1_io
.balign 32
d1_io:
  .zero 64

/* Private key (d) in two shares: d = (d0 + d1) mod n. */
.globl d0
.balign 32
d0:
  .zero 96

.globl d1
.balign 32
d1:
  .zero 96

/* Verification result x_r (aka x_1). */
.globl x_r
.balign 32
x_r:
  .zero 64

/* Secret scalar input buffer. */
.globl k0_io
.balign 32
k0_io:
  .zero 64

.globl k1_io
.balign 32
k1_io:
  .zero 64

/* Secret scalar (k) in two shares: k = (k0 + k1) mod n */
.globl k0
.balign 32
k0:
  .zero 64

.globl k1
.balign 32
k1:
  .zero 64

/* Right side of Weierstrass equation */
.globl rhs
.balign 32
rhs:
  .zero 64

/* Left side of Weierstrass equation */
.globl lhs
.balign 32
lhs:
  .zero 64

/* Temporary storage for P or 2P used in scalar point mult. */
.globl p_temp1
.balign 32
p_temp1:
  .zero 192

/* Temporary storage for P or 2P used in scalar point mult. */
.globl p_temp2
.balign 32
p_temp2:
  .zero 192

.section .scratchpad
/* 704 bytes of scratchpad memory */
.balign 32
.globl scratchpad
scratchpad:
  .zero 896
