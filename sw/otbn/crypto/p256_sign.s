/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_p256.c
 */

.globl p256_sign

.text

 /**
 * P-256 ECDSA signature generation
 *
 * returns the signature as the pair r, s with
 *         r = x_1  mod n
 *     and s = k^(-1)(msg + r*d)  mod n
 *         with x_1 being the affine x-coordinate of the curve point k*G,
 *                  where G is the curve's base point.
 *              k being a supplied secret random number,
 *              n being the order of the base point G of P-256,
 *              msg being the msg to be signed,
 *              d being the private key.
 *
 * This routine runs in constant time.
 *
 * Note: Some versions of the ECDSA spec suggest that msg must be reduced
 * modulo n (e.g. RFC 6979, section 2.4). However, for this implementation, it
 * is sufficient that msg < 2^256, because the message is multiplied with
 * k^(-1) mod n, and our Barrett multiplication implementation accepts any
 * operands a and b such that a * b < 2^256 * p and fully reduces the result.
 *
 * This routine assumes that the secret scalars d and k are provided in two
 * shares each (d0/d1 and k0/k1 respectively), where
 *   d = (d0 + d1) mod n
 *   k = (k0 + k1) mod n
 *
 * Each share is 320 bits, which gives us 64 bits of extra redundancy modulo n
 * (256 bits). This is a protection measure against side-channel attacks.
 *
 * For s = k^-1 * (r * d + msg), we compute a random nonzero masking scalar
 * alpha, and compute s as:
 *   s = ((k * alpha)^-1 * (r * (d * alpha) + alpha * msg)) mod n
 *
 * We choose alpha to be at most 128 bits, so the product with a 320b share
 * produces fits in the same 512-bit modular reduction routine that we use for
 * 256x256-bit multiplications. It should be safe to compute e.g. k * alpha =
 * (k0 * alpha + k1 * alpha) mod n, because alpha has enough randomness to mask
 * the true value of k.
 *
 * @param[in]  dmem[k0]:  first share of secret scalar (320 bits)
 * @param[in]  dmem[k1]:  second share of secret scalar (320 bits)
 * @param[in]  dmem[msg]: message to be signed (256 bits)
 * @param[in]  dmem[r]:   dmem buffer for r component of signature (256 bits)
 * @param[in]  dmem[s]:   dmem buffer for s component of signature (256 bits)
 * @param[in]  dmem[d0]:  first share of private key d (320 bits)
 * @param[in]  dmem[d1]:  second share of private key d (320 bits)
 *
 * Flags: When leaving this subroutine, the M, L and Z flags of FG0 depend on
 *        the computed affine y-coordinate.
 *
 * clobbered registers: x2, x3, x16 to x23, w0 to w26
 * clobbered flag groups: FG0
 */
p256_sign:

  /* init all-zero register */
  bn.xor    w31, w31, w31

  /* load first share of secret scalar k from dmem: w0,w1 = dmem[k0] */
  la        x16, k0
  li        x2, 0
  bn.lid    x2, 0(x16++)
  li        x2, 1
  bn.lid    x2, 0(x16)

  /* load second share of secret scalar k from dmem: w2,w3 = dmem[k1] */
  la        x16, k1
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* setup modulus n (curve order) and Barrett constant
     MOD <= w29 <= n = dmem[p256_n]; w28 <= u_n = dmem[p256_u_n]  */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)
  bn.wsrw   0, w29
  li        x2, 28
  la        x3, p256_u_n
  bn.lid    x2, 0(x3)

  /* scalar multiplication with base point (projective)
     (x_1, y_1, z_1) = (w8, w9, w10) <= k*G = w0*(dmem[p256_gx], dmem[p256_gy]) */
  la        x21, p256_gx
  la        x22, p256_gy
  jal       x1, scalar_mult_int

  /* Convert masked result back to affine coordinates.
     R = (x_a, y_a) = (w11, w12) */
  jal       x1, proj_to_affine

  /* setup modulus n (curve order) and Barrett constant
     MOD <= w29 <= n = dmem[p256_n]; w28 <= u_n = dmem[p256_u_n]  */
  li        x2, 29
  la        x3, p256_n
  bn.lid    x2, 0(x3)
  bn.wsrw   0, w29
  li        x2, 28
  la        x3, p256_u_n
  bn.lid    x2, 0(x3)

  /* re-load first share of secret scalar k from dmem: w0,w1 = dmem[k0] */
  la        x16, k0
  li        x2, 0
  bn.lid    x2, 0(x16++)
  li        x2, 1
  bn.lid    x2, 0(x16)

  /* re-load second share of secret scalar k from dmem: w2,w3 = dmem[k1] */
  la        x16, k1
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* Generate a random 127-bit number.
       w4 <= URND()[255:129] */
  bn.wsrr  w4, 0x2 /* URND */
  bn.rshi  w4, w31, w4 >> 129

  /* Add 1 to get a 128-bit nonzero scalar for masking.
       w4 <= w4 + 1 = alpha */
  bn.addi  w4, w4, 1

  /* w0 <= ([w0,w1] * w4) mod n = (k0 * alpha) mod n */
  bn.mov    w24, w0
  bn.mov    w25, w1
  bn.mov    w26, w4
  jal       x1, mod_mul_320x128
  bn.mov    w0, w19

  /* w19 <= ([w2,w3] * w26) mod n = (k1 * alpha) mod n */
  bn.mov    w24, w2
  bn.mov    w25, w3
  jal       x1, mod_mul_320x128

  /* w0 <= (w0+w19) mod n = (k * alpha) mod n */
  bn.addm   w0, w0, w19

  /* w1 <= w0^-1 mod n = (k * alpha)^-1 mod n */
  jal       x1, mod_inv

  /* Load first share of secret key d from dmem.
       w2,w3 = dmem[d0] */
  la        x16, d0
  li        x2, 2
  bn.lid    x2, 0(x16++)
  li        x2, 3
  bn.lid    x2, 0(x16)

  /* Load second share of secret key d from dmem.
       w5,w6 = dmem[d1] */
  la        x16, d1
  li        x2, 5
  bn.lid    x2, 0(x16++)
  li        x2, 6
  bn.lid    x2, 0(x16)

  /* w0 <= ([w2,w3] * w4) mod n = (d0 * alpha) mod n */
  bn.mov    w24, w2
  bn.mov    w25, w3
  bn.mov    w26, w4
  jal       x1, mod_mul_320x128
  bn.mov    w0, w19

  /* w19 <= ([w5,w6] * w4) mod n = (d1 * alpha) mod n */
  bn.mov    w24, w5
  bn.mov    w25, w6
  bn.mov    w26, w4
  jal       x1, mod_mul_320x128

  /* w0 <= (w0+w19) mod n = (d * alpha) mod n */
  bn.addm   w0, w0, w19

  /* Compare to 0.
     FG0.Z <= (w0 =? w31) = ((d * alpha) mod n =? 0) */
  bn.cmp    w0, w31

  /* Trigger a fault if FG0.Z is set, aborting the computation.

     Since alpha is nonzero mod n, (d * alpha) mod n = 0 means d is zero mod n,
     which violates ECDSA private key requirements. This could technically be
     triggered by an unlucky key manager seed, but the probability is so low (~1/n)
     that it more likely indicates a fault attack. */
  jal       x1, trigger_fault_if_fg0_z

  /* w24 = r <= w11  mod n */
  bn.addm   w24, w11, w31

  /* Store r of signature in dmem.
       dmem[r] <= r = w24 */
  la        x19, r
  li        x2, 24
  bn.sid    x2, 0(x19)

  /* w19 <= (w24 * w0) mod n = (r * d * alpha) mod n */
  bn.mov    w25, w0
  jal       x1, mod_mul_256x256

  /* w0 <= (w1 * w19) mod n = ((k * alpha)^-1 * (r * d * alpha)) mod n
                            = (k^-1 * r * d) mod n */
  bn.mov    w24, w1
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256
  bn.mov    w0, w19

  /* Load message from dmem:
       w24 = msg <= dmem[msg] */
  la        x18, msg
  li        x2, 24
  bn.lid    x2, 0(x18)

  /* w19 = (w24 * w4) mod n = <= (msg * alpha)  mod n */
  bn.mov    w25, w4
  jal       x1, mod_mul_256x256

  /* w19 = (w1 * w19) mod n = ((k * alpha)^-1 * (msg * alpha)) mod n
                            = (k^-1 * msg) mod n */
  bn.mov    w24, w1
  bn.mov    w25, w19
  jal       x1, mod_mul_256x256

  /* w0 = (w0 + w19) mod n = (k^-1*r*d + k^-1*msg) mod n = s */
  bn.addm   w0, w0, w19

  /* Store s of signature in dmem.
       dmem[s] <= s = w0 */
  la        x20, s
  li        x2, 0
  bn.sid    x2, 0(x20)

  ret

.section .bss

/* random scalar k (in two 320b shares) */
.balign 32
.weak k0
k0:
  .zero 64
.balign 32
.weak k1
k1:
  .zero 64

/* message digest */
.balign 32
.weak msg
msg:
  .zero 32

/* signature R */
.balign 32
.weak r
r:
  .zero 32

/* signature S */
.balign 32
.weak s
s:
  .zero 32

/* private key d (in two 320b shares) */
.balign 32
.weak d0
d0:
  .zero 64
.balign 32
.weak d1
d1:
  .zero 64
