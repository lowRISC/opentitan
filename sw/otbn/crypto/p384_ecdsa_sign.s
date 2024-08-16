/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-384 ECDSA signing operations.
 *
 * This binary generates a signature using a caller-provided secret key.
 *
 * This binary has the following modes of operation:
 * 1. MODE_SIGN: generate signature using caller-provided secret key
 * 2. MODE_SIDELOAD_SIGN: generate signature using sideloaded secret key/seed
 */

 /**
 * Mode magic values, generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 5 -n 11 \
 *     --avoid-zero -s 2205231843
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_SIGN, 0x15b
.equ MODE_SIDELOAD_SIGN, 0x49e

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_SIGN
.globl MODE_SIDELOAD_SIGN

.section .text.start
.globl start
start:
  /* Init all-zero register. */
  bn.xor    w31, w31, w31

  /* Read the mode and tail-call the requested operation. */
  la    x2, mode
  lw    x2, 0(x2)

  addi  x3, x0, MODE_SIGN
  beq   x2, x3, ecdsa_sign

  addi  x3, x0, MODE_SIDELOAD_SIGN
  beq   x2, x3, ecdsa_sign_sideload

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp

/**
 * P-384 ECDSA signature generation.
 * Generate the secret scalar k from a random seed.
 *
 * @param[in]  dmem[msg]: message to be signed in dmem
 * @param[in]   dmem[d0]: 1st private key share d0
 * @param[in]   dmem[d1]: 2nd private key share d1
 * @param[out]   dmem[r]: r component of signature
 * @param[out]   dmem[s]: s component of signature
 */
ecdsa_sign:
  /* Generate a fresh random scalar for signing.
       dmem[k0] <= first share of k
       dmem[k1] <= second share of k */
  jal      x1, p384_generate_k

  /* Generate the signature. */
  jal      x1, p384_sign

  ecall

/**
 * P-384 ECDSA side-loaded signature generation.
 * Generate a signature using a private key from a
 * sideloaded seed.
 *
 * @param[in]  dmem[msg]: message to be signed in dmem
 * @param[out]   dmem[r]: r component of signature
 * @param[out]   dmem[s]: s component of signature
 */
ecdsa_sign_sideload:
  /* Load keymgr seeds from WSRs.
       w20,w21 <= seed0
       w10,w11 <= seed1 */
  bn.wsrr   w20, KEY_S0_L
  bn.wsrr   w21, KEY_S0_H
  bn.wsrr   w10, KEY_S1_L
  bn.wsrr   w11, KEY_S1_H

  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, p384_key_from_seed

  /* Tail-call signature-generation routine. */
  jal       x0, ecdsa_sign


.bss

/* Operational mode. */
.globl mode
.balign 4
mode:
  .zero 4

/* x-coordinate. */
.globl x
.balign 32
x:
  .zero 64

/* y-coordinate. */
.globl y
.balign 32
y:
  .zero 64

/* random scalar first share */
.globl k0
.balign 32
k0:
  .zero 64

/* random scalar second share */
.globl k1
.balign 32
k1:
  .zero 64

/* r part of signature */
.globl r
.balign 32
r:
  .zero 64

/* s part of signature */
.globl s
.balign 32
s:
  .zero 64

.data

/* private key first share */
.globl d0
.balign 32
d0:
  .zero 64

/* private key second share */
.globl d1
.balign 32
d1:
  .zero 64

/* hash message to sign/verify */
.globl msg
.balign 32
msg:
  .zero 64

/* 704 bytes of scratchpad memory
  defined globally to save dmem */
.balign 32
.globl scratchpad
scratchpad:
  .zero 704
