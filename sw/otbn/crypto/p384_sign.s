/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
 *   P-384 specific routines for ECDSA signature generation.
 */

 .section .text

/**
 * P-384 ECDSA signature generation
 *
 * returns the signature as the pair r, s with
 *         r = x_1  mod n
 *     and s = k^(-1)(msg + r*d)  mod n
 *         where x_1 is the affine x-coordinate of the curve point k*G,
 *               G is the curve's base point,
 *               k is a supplied secret random number,
 *               n is the order of the base point G of P-256,
 *               msg is the message to be signed, and
 *               d is the private key.
 *
 * This routine runs in constant time.
 *
 * @param[in]  dmem[k0]: 1st scalar share k0 in dmem
 * @param[in]  dmem[k1]: 2nd scalar share k1 in dmem
 * @param[in] dmem[msg]: message to be signed in dmem
 * @param[in]  dmem[d0]: 1st private key share d0 in dmem
 * @param[in]  dmem[d1]: 2nd private key share d1 in dmem
 * @param[out]  dmem[r]: r component of signature
 * @param[out]  dmem[s]: s component of signature
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * clobbered registers: x2 to x6, x9 to x15, x17 to x28, x30
 *                      w0 to w31
 * clobbered flag groups: FG0
 */
.globl p384_sign
p384_sign:
  /* init all-zero reg */
  bn.xor    w31, w31, w31

  /* get dmem pointer of domain parameter b */
  la        x28, p384_b

  /* get dmem pointer of base point x-coordinate */
  la        x20, p384_gx

  /* get dmem pointer of base point y-coordinate */
  la        x21, p384_gy

  /* get dmem pointer of scratchpad */
  la        x30, scratchpad

  /* get dmem pointer of 1st scalar share k0 */
  la        x17, k0

  /* get dmem pointer of 1st scalar share k1 */
  la        x19, k1

  /* get dmem pointer of message */
  la        x6, msg

  /* get dmem pointer of r component */
  la        x14, r

  /* get dmem pointer of s component */
  la        x15, s

  /* get dmem pointer of 1st private key share d0 */
  la        x4, d0

  /* get dmem pointer of 1st private key share d0 */
  la        x5, d1

  /* load domain parameter p (modulus)
     [w13, w12] <= p = dmem[dptr_p] */
  li        x2, 12
  la        x3, p384_p
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* load domain parameter n (order of base point)
     [w11, w10] = n = dmem[p384_n] */
  li        x2, 10
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* scalar multiplication with base point and
     conversion of projective coordinates to affine space
     [w28:w25] <= (R_x, R_y) = k * G */
  jal       x1, scalar_mult_int_p384
  jal       x1, proj_to_affine_p384

  /* store r of signature in dmem: dmem[dptr_r] <= r = R_x = [w26,w25] */
  li        x2, 25
  bn.sid    x2++, 0(x14)
  bn.sid    x2++, 32(x14)

  /* load domain parameter n (order of base point)
     [w13, w12] <= n = dmem[p384_n] */
  li        x2, 12
  la        x3, p384_n
  bn.lid    x2++, 0(x3)
  bn.lid    x2++, 32(x3)

  /* Compute Solinas constant k for modulus n (we know it is only 191 bits, so
     no need to compute the high part):
     w14 <= 2^256 - n[255:0] = (2^384 - n) mod (2^256) = 2^384 - n */
  bn.sub    w14, w31, w12

  /* Multiplicative masking of shares k0 and k1 */

  /* Generate a random 127-bit number.
     w4 <= URND()[255:129] */
  bn.wsrr   w4, URND
  bn.rshi   w4, w31, w4 >> 129

  /* Add 1 to get a 128-bit nonzero scalar for masking.
     w4 <= w4 + 1 = alpha */
  bn.addi   w4, w4, 1

  /* load 1st share k0 from dmem
     [w11,w10] <= k0 = dmem[dptr_k0] */
  li        x2, 10
  bn.lid    x2++, 0(x17)
  bn.lid    x2++, 32(x17)

  /* [w26,w25] <= ([w11,w10] * w4) mod n = (k0 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w25, w16
  bn.mov    w26, w17

  /* load 2nd share k1 from dmem
     [w11,w10] <= k1 = dmem[dptr_k1] */
  li        x2, 10
  bn.lid    x2++, 0(x19)
  bn.lid    x2++, 32(x19)

  /* [w28,w27] <= ([w11,w10] * w4) mod n = (k1 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w27, w16
  bn.mov    w28, w17

  /* Multiplicative masking of shares d0 and d1 */

  /* load 1st share d0 from dmem
     [w11,w10] <= d0 = dmem[dptr_d0] */
  li        x2, 10
  bn.lid    x2++, 0(x4)
  bn.lid    x2++, 32(x4)

  /* [w7,w6] <= ([w11,w10] * w4) mod n = (d0 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w6, w16
  bn.mov    w7, w17

  /* load 2nd share d1 from dmem
     [w11,w10] <= d1 = dmem[dptr_d1] */
  li        x2, 10
  bn.lid    x2++, 0(x5)
  bn.lid    x2++, 32(x5)

  /* [w9,w8] <= ([w11,w10] * w4) mod n = (d1 * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w8, w16
  bn.mov    w9, w17

  /* Multiplicative masking of message msg */

  /* load message from dmem
     [w11, w10] <= msg = dmem[dptr_msg] */
  li        x2, 10
  bn.lid    x2++, 0(x6)
  bn.lid    x2++, 32(x6)

  /* [w1,w0] <= ([w11,w10] * w4) mod n = (msg * alpha) mod n */
  bn.mov    w16, w4
  jal       x1, p384_mulmod448x128_n
  bn.mov    w0, w16
  bn.mov    w1, w17

  /* Compute (k*alpha) mod n = (k0*alpha + k1*alpha) mod n
     [w17,w16] <= k*alpha = [w26,w25] + [w28,w27] mod n */
  bn.add    w18, w27, w25
  bn.addc   w19, w28, w26
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* modular multiplicative inverse of k
     [w3, w2] <= [w17, w16] <= (k*alpha)^(-1) mod n */
  bn.mov    w29, w16
  bn.mov    w30, w17
  jal       x1, mod_inv_n_p384
  bn.mov    w2, w16
  bn.mov    w3, w17

  /* Compute (d*alpha) mod n = (d0*alpha + d1*alpha) mod n
     [w17,w16] <= d*alpha = [w7,w6] + [w9,w8] mod n */
  bn.add    w18, w8, w6
  bn.addc   w19, w9, w7
  bn.mov    w20, w31
  jal       x1, p384_reduce_n

  /* [w17, w16] <= (k*alpha)^(-1)*d*alpha mod n = [w3, w2] * [w17, w16] mod [w13, w12] */
  bn.mov    w10, w2
  bn.mov    w11, w3
  jal       x1, p384_mulmod_n

  /* load r of signature from dmem
     [w11,w10] <= r = dmem[dptr_r] */
  li        x2, 10
  bn.lid    x2++, 0(x14)
  bn.lid    x2++, 32(x14)

  /*  [w5, w4] <= [w17, w16]
        <= r * (k^(-1)*d) mod n = r * ((k*alpha)^(-1)*d*alpha) mod n =
           = [w11, w10] * [w17, w16] mod [w13, w12] */
  jal       x1, p384_mulmod_n
  bn.mov    w4, w16
  bn.mov    w5, w17

  /* [w17, w16] <= k^(-1) * msg =
                   = (k*alpha)^(-1) * msg*alpha =
                   = [w3, w2]*[w1, w0] mod n */
  bn.mov    w10, w0
  bn.mov    w11, w1
  bn.mov    w16, w2
  bn.mov    w17, w3
  jal       x1, p384_mulmod_n

  /* [w28, w27] <= s' = k^(-1)*msg + k^(-1)*r*d  = [w17, w16] + [w5, w4]*/
  bn.add    w27, w16, w4
  bn.addc   w28, w17, w5

  /* reduce s: [w28, w27] <= s <= s' mod n = [w28, w27] mod [w13, w12] */
  bn.sub    w10, w27, w12
  bn.subb   w11, w28, w13
  bn.sel    w27, w27, w10, C
  bn.sel    w28, w28, w11, C

  /* store s of signature in dmem: dmem[dptr_s] <= s = [w28, w27] */
  li        x2, 27
  bn.sid    x2++, 0(x15)
  bn.sid    x2++, 32(x15)

  ret


/* scratchpad memory */
.section .data

.balign 32

/* message to be signed */
.globl msg
.weak msg
msg:
  .zero 64

/* r component of signature */
.globl r
.weak r
r:
  .zero 64

/* s component of signature */
.globl s
.weak s
s:
  .zero 64

/* 1st scalar share d0 */
.globl k0
.weak k0
k0:
  .zero 64

/* 2nd scalar share d1 */
.globl k1
.weak k1
k1:
  .zero 64

/* 1st private key share d0 */
.globl d0
.weak d0
d0:
  .zero 64

/* 2nd private key share d1 */
.globl d1
.weak d1
d1:
  .zero 64

/* 704 bytes of scratchpad memory */
.balign 32
.globl scratchpad
.weak scratchpad
scratchpad:
  .zero 704
