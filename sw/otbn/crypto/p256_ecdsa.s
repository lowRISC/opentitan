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
 * @param[in]  dmem[msg]: message to be verified (256 bits)
 * @param[in]  dmem[r]:   r component of signature (256 bits)
 * @param[in]  dmem[s]:   s component of signature (256 bits)
 * @param[in]  dmem[x]:   affine x-coordinate of public key (256 bits)
 * @param[in]  dmem[y]:   affine y-coordinate of public key (256 bits)
 * @param[out] dmem[x_r]: dmem buffer for reduced affine x_r-coordinate (x_1)
 */
ecdsa_verify:
  /* Validate the public key. */
  jal      x1, check_public_key_valid

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
  bn.wsrr  w20, 4 /*KEY_S0_L*/
  bn.wsrr  w21, 5 /*KEY_S0_H*/
  bn.wsrr  w10, 6 /*KEY_S1_L*/
  bn.wsrr  w11, 7 /*KEY_S1_H*/

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

/**
 * Check if a provided public key is valid.
 *
 * For a given public key (x, y), check that:
 * - x and y are both fully reduced mod p
 * - (x, y) is on the P-256 curve.
 *
 * Note that, because the point is in affine form, it is not possible that (x,
 * y) is the point at infinity. In some other forms such as projective
 * coordinates, we would need to check for this also.
 *
 * This routine raises a software error and halts operation if the public key
 * is invalid.
 *
 * @param[in] dmem[x]: Public key x-coordinate.
 * @param[in] dmem[y]: Public key y-coordinate.
 */
check_public_key_valid:
  /* Init all-zero register. */
  bn.xor   w31, w31, w31

  /* Load domain parameter p.
       w29 <= dmem[p256_p] = p */
  li        x2, 29
  la        x3, p256_p
  bn.lid    x2, 0(x3)

  /* Load public key x-coordinate.
       w2 <= dmem[x] = x */
  li        x2, 2
  la        x3, x
  bn.lid    x2, 0(x3)

  /* Compare x to p.
       FG0.C <= (x < p) */
  bn.cmp    w2, w29

  /* Trigger a fault if FG0.C is false. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1
  bne       x2, x0, _x_valid
  unimp

  _x_valid:

  /* Load public key y-coordinate.
       w2 <= dmem[y] = y */
  li        x2, 2
  la        x3, y
  bn.lid    x2, 0(x3)

  /* Compare y to p.
       FG0.C <= (y < p) */
  bn.cmp    w2, w29

  /* Trigger a fault if FG0.C is false. */
  csrrs     x2, FG0, x0
  andi      x2, x2, 1
  bne       x2, x0, _y_valid
  unimp

  _y_valid:

  /* Save the signature values to registers.
       w4 <= dmem[r]
       w5 <= dmem[s] */
  li        x2, 4
  la        x3, r
  bn.lid    x2++, 0(x3)
  la        x3, s
  bn.lid    x2, 0(x3)

  /* Compute both sides of the Weierstrauss equation.
       dmem[r] <= (x^3 + ax + b) mod p
       dmem[s] <= (y^2) mod p */
  jal      x1, p256_isoncurve

  /* Load both sides of the equation.
       w2 <= dmem[r]
       w3 <= dmem[s] */
  li        x2, 2
  la        x3, r
  bn.lid    x2++, 0(x3)
  la        x3, s
  bn.lid    x2, 0(x3)

  /* Compare the two sides of the equation.
       FG0.Z <= (y^2) mod p == (x^2 + ax + b) mod p */
  bn.cmp    w2, w3

  /* Trigger a fault if FG0.Z is false. */
  csrrs     x2, FG0, x0
  srli      x2, x2, 3
  andi      x2, x2, 1
  bne       x2, x0, _pk_valid
  unimp

  _pk_valid:

  /* Write back the saved signature values.
       dmem[r] <= w4
       dmem[s] <= w5 */
  li        x2, 4
  la        x3, r
  bn.sid    x2++, 0(x3)
  la        x3, s
  bn.sid    x2, 0(x3)

  ret

.bss

/* Operation mode. */
.globl mode
.balign 4
mode:
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
