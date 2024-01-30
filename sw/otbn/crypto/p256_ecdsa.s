/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-256 ECDSA operations.
 *
 * This binary has the following modes of operation:
 * 1. MODE_KEYGEN: generate a new keypair
 * 2. MODE_SIGN: generate signature using caller-provided secret key
 * 3. MODE_VERIFY: verify a signature
 * 4. MODE_SIDELOAD_KEYGEN: generate a keypair from a sideloaded seed
 * 5. MODE_SIDELOAD_SIGN: compute shared key using sideloaded seed
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
.equ MODE_KEYGEN, 0x3d4
.equ MODE_SIGN, 0x15b
.equ MODE_VERIFY, 0x727
.equ MODE_SIDELOAD_KEYGEN, 0x5e8
.equ MODE_SIDELOAD_SIGN, 0x49e

.section .text.start
.globl start
start:
  /* Read the mode and tail-call the requested operation. */
  la    x2, mode
  lw    x2, 0(x2)

  addi  x3, x0, MODE_KEYGEN
  beq   x2, x3, random_keygen

  addi  x3, x0, MODE_SIGN
  beq   x2, x3, ecdsa_sign

  addi  x3, x0, MODE_VERIFY
  beq   x2, x3, ecdsa_verify

  addi  x3, x0, MODE_SIDELOAD_KEYGEN
  beq   x2, x3, sideload_keygen

  addi  x3, x0, MODE_SIDELOAD_SIGN
  beq   x2, x3, sideload_ecdsa_sign

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp

/**
 * Generate a fresh, random keypair.
 *
 * @param[out] dmem[d0]: First share of secret key.
 * @param[out] dmem[d1]: Second share of secret key.
 * @param[out]  dmem[x]: Public key x-coordinate.
 * @param[out]  dmem[y]: Public key y-coordinate.
 */
random_keygen:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal      x1, p256_generate_random_key

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal      x1, p256_base_mult

  ecall

/**
 * Generate a signature.
 *
 * @param[in]  dmem[msg]: message to be signed (256 bits)
 * @param[in]  dmem[r]:   dmem buffer for r component of signature (256 bits)
 * @param[in]  dmem[s]:   dmem buffer for s component of signature (256 bits)
 * @param[in]  dmem[d0]:  first share of private key d (320 bits)
 * @param[in]  dmem[d1]:  second share of private key d (320 bits)
 */
ecdsa_sign:
  /* Generate a fresh random scalar for signing.
       dmem[k0] <= first share of k
       dmem[k1] <= second share of k */
  jal      x1, p256_generate_k

  /* Generate the signature. */
  jal      x1, p256_sign

  ecall

/**
 * Verify a signature.
 *
 * The result of the verification is returned in two variables: `ok`
 * indicates whether the signature passed basic validity checks, and `x_r`
 * indicates the recovered value. A signature passes verification only if BOTH:
 * - `ok` is true, and
 * - `x_r` is equal to the original `r` value.
 *
 * If `ok` is false, the value in `x_r` is meaningless; callers
 * should check both.
 *
 * @param[in]  dmem[msg]: message to be verified (256 bits)
 * @param[in]  dmem[r]:   r component of signature (256 bits)
 * @param[in]  dmem[s]:   s component of signature (256 bits)
 * @param[in]  dmem[x]:   affine x-coordinate of public key (256 bits)
 * @param[in]  dmem[y]:   affine y-coordinate of public key (256 bits)
 * @param[out] dmem[ok]:  success/failure of basic checks (32 bits)
 * @param[out] dmem[x_r]: dmem buffer for reduced affine x_r-coordinate (x_1)
 */
ecdsa_verify:
  /* Validate the public key (ends the program on failure). */
  jal      x1, p256_check_public_key

  /* Verify the signature (compute x_r). */
  jal      x1, p256_verify

  ecall

/**
 * Generate a keypair from a sideloaded seed.
 *
 * @param[out] dmem[d0]: First share of secret key.
 * @param[out] dmem[d1]: Second share of secret key.
 * @param[out]  dmem[x]: Public key x-coordinate.
 * @param[out]  dmem[y]: Public key y-coordinate.
 */
sideload_keygen:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal   x1, secret_key_from_seed

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal      x1, p256_base_mult

  ecall

/**
 * Generate a signature using a private key from a sideloaded seed.
 *
 * @param[in]  dmem[msg]: message to be signed (256 bits)
 * @param[in]  dmem[r]:   dmem buffer for r component of signature (256 bits)
 * @param[in]  dmem[s]:   dmem buffer for s component of signature (256 bits)
 */
sideload_ecdsa_sign:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal   x1, secret_key_from_seed

  /* Tail-call signature-generation routine. */
  jal      x0, ecdsa_sign

/**
 * Generate a secret key from a keymgr-derived seed.
 *
 * @param[out] dmem[d0]: First share of secret key.
 * @param[out] dmem[d0]: Second share of secret key.
 */
secret_key_from_seed:
  /* Load keymgr seeds from WSRs.
       w20,w21 <= seed0
       w10,w11 <= seed1 */
  bn.wsrr  w20, KEY_S0_L
  bn.wsrr  w21, KEY_S0_H
  bn.wsrr  w10, KEY_S1_L
  bn.wsrr  w11, KEY_S1_H

  /* Init all-zero register. */
  bn.xor   w31, w31, w31

  /* Generate secret key shares.
       w20, w21 <= d0
       w10, w11 <= d1 */
  jal      x1, p256_key_from_seed

  /* Store secret key shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  li       x2, 20
  la       x3, d0
  bn.sid   x2++, 0(x3)
  bn.sid   x2++, 32(x3)
  li       x2, 10
  la       x3, d1
  bn.sid   x2++, 0(x3)
  bn.sid   x2, 32(x3)

  ret

.bss

/* Operation mode. */
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
  .zero 32

/* Signature R. */
.globl r
.balign 32
r:
  .zero 32

/* Signature S. */
.globl s
.balign 32
s:
  .zero 32

/* Public key x-coordinate. */
.globl x
.balign 32
x:
  .zero 32

/* Public key y-coordinate. */
.globl y
.balign 32
y:
  .zero 32

/* Private key (d) in two shares: d = (d0 + d1) mod n. */
.globl d0
.balign 32
d0:
  .zero 64
.globl d1
.balign 32
d1:
  .zero 64

/* Verification result x_r (aka x_1). */
.globl x_r
.balign 32
x_r:
  .zero 32

.section .scratchpad

/* Secret scalar (k) in two shares: k = (k0 + k1) mod n */
.globl k0
.balign 32
k0:
  .zero 64

.globl k1
.balign 32
k1:
  .zero 64
