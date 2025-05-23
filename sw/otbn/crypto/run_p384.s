/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Entrypoint for P-384 ECDH and ECDSA operations.
 *
 * This binary has the following modes of operation:
 * 1. MODE_KEYGEN: generate a new keypair
 * 2. MODE_SIGN: generate an ECDSA signature using caller-provided secret key
 * 3. MODE_VERIFY: verify an ECDSA signature
 * 4. MODE_ECDH: ECDH key exchange using a caller-provided secret key
 * 5. MODE_SIDELOAD_KEYGEN: generate a keypair from a sideloaded seed
 * 6. MODE_SIDELOAD_SIGN: generate an ECDSA signature using sideloaded secret key/seed
 * 7. MODE_SIDELOAD_ECDH: ECDH key exchange using a secret key from a sideloaded seed
 */

/**
 * Mode magic values generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 4 -n 11 --avoid-zero -s 1654842154
 *
 * Call the same utility with the same arguments and a higher -m to generate
 * additional value(s) without changing the others or sacrificing mutual HD.
 *
 * TODO(#17727): in some places the OTBN assembler support for .equ directives
 * is lacking, so they cannot be used in bignum instructions or pseudo-ops such
 * as `li`. If support is added, we could use 32-bit values here instead of
 * 11-bit.
 */
.equ MODE_KEYGEN, 0x0e7
.equ MODE_SIGN, 0x633
.equ MODE_VERIFY, 0x54d
.equ MODE_ECDH, 0x3bd
.equ MODE_SIDELOAD_KEYGEN, 0x4da
.equ MODE_SIDELOAD_SIGN, 0x786
.equ MODE_SIDELOAD_ECDH, 0x36a

/**
 * Make the mode constants visible to Ibex.
 */
.globl MODE_KEYGEN
.globl MODE_SIGN
.globl MODE_VERIFY
.globl MODE_ECDH
.globl MODE_SIDELOAD_KEYGEN
.globl MODE_SIDELOAD_SIGN
.globl MODE_SIDELOAD_ECDH

/**
 * Hardened boolean values.
 *
 * Should match the values in `hardened_asm.h`.
 */
.equ HARDENED_BOOL_TRUE, 0x739
.equ HARDENED_BOOL_FALSE, 0x1d4

.section .text.start
.globl start
start:
  /* Read the mode and tail-call the requested operation. */
  la    x2, mode
  lw    x2, 0(x2)

  addi  x3, x0, MODE_KEYGEN
  beq   x2, x3, keypair_random

  addi  x3, x0, MODE_VERIFY
  beq   x2, x3, ecdsa_verify

  addi  x3, x0, MODE_SIDELOAD_KEYGEN
  beq   x2, x3, keypair_from_seed

  addi  x3, x0, MODE_SIDELOAD_SIGN
  beq   x2, x3, ecdsa_sign_sideloaded

  addi  x3, x0, MODE_SIDELOAD_ECDH
  beq   x2, x3, shared_key_from_seed

  /* Copy the caller-provided secret key shares into scratchpad memory.
       dmem[d0] <= dmem[d0_io]
       dmem[d1] <= dmem[d1_io] */
  la       x13, d0_io
  la       x14, d0
  jal      x1, copy_share
  la       x13, d1_io
  la       x14, d1
  jal      x1, copy_share

  addi  x3, x0, MODE_SIGN
  beq   x2, x3, ecdsa_sign

  addi  x3, x0, MODE_ECDH
  beq   x2, x3, shared_key

  /* Invalid mode; fail. */
  unimp
  unimp
  unimp

/**
 * Helper routine to copy secret key shares.
 *
 * Copies 64 bytes from the source to destination location in DMEM. The source
 * and destination may be the same but should not otherwise overlap.
 *
 * @param x13: dptr_src, pointer to source DMEM location
 * @param x14: dptr_dst, pointer to destination DMEM location
 * @param      dmem[dptr_src..dptr_src+64]: source data
 * @param[out] dmem[dptr_dst..dptr_dst+64]: copied data
 *
 * clobbered registers: x10, w10
 * clobbered flag groups: none
 */
copy_share:
  /* Randomize the content of w10 to prevent leakage. */
  bn.wsrr  w10, URND

  /* Copy the secret key shares into Ibex-visible memory. */
  li       x10, 10
  bn.lid   x10, 0(x13)
  bn.sid   x10, 0(x14)
  bn.lid   x10, 32(x13)
  bn.sid   x10, 32(x14)
  ret

/**
 * Generate a fresh random keypair.
 *
 * Returns secret key d in 448-bit shares d0, d1.
 *
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * This routine runs in constant time (except potentially waiting for entropy
 * from RND).
 *
 * @param[in]        w31: all-zero
 * @param[out]  dmem[d0]: 1st private key share d0
 * @param[out]  dmem[d1]: 2nd private key share d1
 * @param[out]   dmem[x]: Public key x-coordinate
 * @param[out]   dmem[y]: Public key y-coordinate
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
keypair_random:
  /* Generate secret key d in shares.
       dmem[d0] <= d0
       dmem[d1] <= d1 */
  jal       x1, p384_generate_random_key

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal       x1, p384_base_mult

  /* Copy the secret key shares into Ibex-visible memory.
       dmem[d0_io] <= dmem[d0]
       dmem[d1_io] <= dmem[d1] */
  la       x13, d0
  la       x14, d0_io
  jal      x1, copy_share
  la       x13, d1
  la       x14, d1_io
  jal      x1, copy_share

  ecall

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
 *
 * Generate a signature using a private key from a
 * sideloaded seed.
 *
 * @param[in]  dmem[msg]: message to be signed in dmem
 * @param[out]   dmem[r]: r component of signature
 * @param[out]   dmem[s]: s component of signature
 */
ecdsa_sign_sideloaded:
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

/**
 * P-384 ECDSA signature verification
 *
 * The routine computes the x1 coordinate and places it in dmem. x1 will be
 * reduced (mod n), however, the final comparison has to be performed on the
 * host side. The signature is valid if x1 == r.
 * This routine runs in variable time.
 *
 * @param[in]  dmem[msg]: message to be verified
 * @param[in]    dmem[r]: r part of signature
 * @param[in]    dmem[s]: s part of signature
 * @param[in]    dmem[x]: x-coordinate of public key
 * @param[in]    dmem[y]: y-coordinate of public key
 * @param[out] dmem[x_r]: x1 coordinate to be compared to rs
 */
ecdsa_verify:
  /* Validate the public key (ends the program on failure). */
  jal      x1, p384_check_public_key

  /* Verify the signature (compute x1). */
  jal      x1, p384_verify

  ecall


/**
 * Generate a shared key from a secret and public key.
 *
 * Returns the shared key, which is the affine x-coordinate of (d*Q). The
 * shared key is expressed in boolean shares x0, x1 such that the key is (x0 ^
 * x1).
 *
 * This routine runs in constant time.
 *
 * @param[in]        w31: all-zero
 * @param[in]   dmem[d0]: 1st private key share d0
 * @param[in]   dmem[d1]: 2nd private key share d1
 * @param[in]    dmem[x]: x-coordinate of public key
 * @param[in]    dmem[y]: y-coordinate of public key
 * @param[out]   dmem[x]: x0, first share of shared key.
 * @param[out]   dmem[y]: x1, second share of shared key.
 *
 * clobbered registers: x2, x3, x9 to x13, x17 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
shared_key:
  /* Validate the public key (ends the program on failure). */
  jal      x1, p384_check_public_key

  /* If we got here the basic validity checks passed, so set `ok` to true. */
  la       x2, ok
  addi     x3, x0, HARDENED_BOOL_TRUE
  sw       x3, 0(x2)

  /* Generate arithmetically masked shared key d*Q.
     dmem[x] <= (d*Q).x - m mod p
     dmem[y] <= m */
  jal       x1, p384_scalar_mult

  /* Arithmetic-to-boolean conversion*/

  /* load result to WDRs for a2b conversion.
     [w12,w11] <= dmem[x] = x_m
     [w19,w18] <= dmem[y] = m */
  li        x2, 11
  la        x3, x
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)
  li        x2, 18
  la        x3, y
  bn.lid    x2++, 0(x3)
  bn.lid    x2, 32(x3)

  /* Load domain parameter.
     [w14,w13] = dmem[p384_p] */
  li        x2, 13
  la        x4, p384_p
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  jal       x1, p384_arithmetic_to_boolean_mod

  /* Store arithmetically masked key to DMEM
     dmem[x] <= [w21,w20] = x_m' */
  li        x2, 20
  la        x3, x
  bn.sid    x2++, 0(x3)
  bn.sid    x2++, 32(x3)

  ecall

/**
 * Generate a fresh random keypair from a sideloaded seed.
 *
 * Returns secret key d in 384-bit shares d0, d1.
 *
 * Returns public key Q = d*G in affine coordinates (x, y).
 *
 * This routine runs in constant time (except potentially waiting for entropy
 * from RND).
 *
 * @param[in]       w31: all-zero
 * @param[out] dmem[d0]: 1st private key share d0
 * @param[out] dmem[d1]: 2nd private key share d1
 * @param[out]  dmem[x]: Public key x-coordinate
 * @param[out]  dmem[y]: Public key y-coordinate
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
keypair_from_seed:
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

  /* Generate public key d*G.
       dmem[x] <= (d*G).x
       dmem[y] <= (d*G).y */
  jal       x1, p384_base_mult

  ecall

/**
 * Generate a shared key from a fresh secret key with sideloaded seed
 * and a given public key.
 *
 * Returns the shared key, which is the affine x-coordinate of (d*Q). The
 * shared key is expressed in boolean shares x0, x1 such that the key is (x0 ^
 * x1).
 * Returns secret key d in 384-bit shares d0, d1.
 *
 * This routine runs in constant time.
 *
 * @param[in]        w31: all-zero
 * @param[out]   dmem[x]: x0, first share of shared key.
 * @param[out]   dmem[y]: x1, second share of shared key.
 *
 * clobbered registers: x2, x3, x9 to x13, x18 to x21, x26 to x30, w0 to w30
 * clobbered flag groups: FG0
 */
shared_key_from_seed:
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

  /* Jump to shared key computation. */
  jal       x0, shared_key


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

/* Verification result x_r (aka x_1). */
.globl x_r
.balign 32
x_r:
  .zero 64

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

/* Private key (d) in two shares: d = (d0 + d1) mod n. */
.globl d0
.balign 32
d0:
  .zero 64
.globl d1
.balign 32
d1:
  .zero 64
