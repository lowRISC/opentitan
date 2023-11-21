/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library contains arithmetic for the scalar field of the Ed25519
 * signature scheme, which is modulo the curve order L:
 *
 *   L = 2^252+27742317777372353535851937790883648493 (see RFC 8032, section 5.1)
 *
 * Elements of this field are used for scalar multiplication of curve points.
 * The scalar field should not be confused with the field used for curve
 * coordinates, which is modulo p = 2^255 - 19.
 */


/**
 * Load constants for the scalar field.
 *
 * This routine should run before any other operations in this field are used,
 * and again if its output is subsequently overwritten.
 *
 * This routine runs in constant time.
 *
 * @param[in]  w31: all-zero
 * @param[out] [w15:w14]: mu = floor(2^512 / L) (precomputed constant)
 * @param[out] MOD: L, modulus
 *
 * clobbered registers: x2, x3, w14, w15, MOD
 * clobbered flag groups: FG0
 */
.globl sc_init
sc_init:
  /* Load modulus L into the MOD register. */
  li      x2, 14
  la      x3, ed25519_scalar_L
  bn.lid  x2, 0(x3)
  bn.wsrw MOD, w14

  /* Load lower half of precomputed constant mu (260 bits).
       w14 <= mu mod 2^256 */
  la      x3, ed25519_scalar_mu_low
  bn.lid  x2, 0(x3)

  /* Higher half of mu is very small (15), so we can simply use addi here.
       w15 <= 15 = mu >> 256 */
  bn.addi w15, w31, 15

  ret

/**
 * Fully reduce a 512-bit number modulo L.
 *
 * Returns c = a mod L.
 *
 * Uses the Barrett reduction algorithm according to the Handbook of Applied
 * Cryptography, section 14.3.3:
 *   https://cacr.uwaterloo.ca/hac/about/chap14.pdf
 *
 * For this use-case, b=2^256 and k=1. We will use two constant-time
 * conditional subtractions instead of a while loop at the end (HAC shows that
 * a maximum of two are needed). Keeping the same variable names but slightly
 * simplifying the expression, the algorithm becomes:
 *
 * mu <- floor((2^512) / L) (precomputed)
 * q3 <- (x * mu) >> 512
 * r2 <- (q3 * L) mod 2^512
 * r <- x + (r2 < r1 ? 2^512 : 0) - r2
 * r <- r < L ? r : r - L
 * r <- r < L ? r : r - L
 * return r
 *
 * The conceptual strategy here is that we use the precomputed constant mu to
 * estimate the quotient  Q = floor(x / L). Above, the variable named "q3" is
 * the estimated quotient, which can be proven to be off by at most two; as
 * stated in HAC, Q - 2 <= q3 <= Q. From there, we can use the estimated
 * quotient to estimate the remainder (x mod L = x - Q * L):
 *
 *   x - Q * L <= x - (q3 * L) <= x - (Q - 2) * L
 *   x mod L   <= x - (q3 * L) <= x mod L + 2 * L
 *
 * Since we know that (x - (q3 * L) < 2^512), we lose no precision by computing
 * the product and subtraction modulo 2^512, and we save a few instructions.
 * In fact, in this specific case, we can take this idea farther; L is only 253
 * bits, so the upper bound of r (x mod L + 2 * L) is guaranteed to fit in 256
 * bits. Therefore, it is sufficient to compute (x - (q3 * L)) modulo 2^256,
 * which is what this implementation does.
 *
 * The algorithm used here, as described above, has been checked in the Coq
 * proof assistant:
 * https://gist.github.com/jadephilipoom/f70e740fbe885bf8b040374eca27a456
 *
 * Note that the proof covers only the algorithm; it doesn't have the exact
 * instructions or a machine model of OTBN. The algorithm definition and the
 * proven specification are reproduced below:
 *
 * Definition sc_reduce (x : N) :=
 *   let q2 := x * mu in
 *   let q3 := (q2 / (2 ^ 512)) in
 *   let r1 := x mod 2^256 in
 *   let r2 := (q3 * L) mod (2 ^ 256) in
 *   let r := r1 + (if r1 <? r2 then 2 ^ 256 else 0) - r2 in
 *   let r := if r <? L then r else r - L in
 *   let r := if r <? L then r else r - L in
 *   r.
 *
 * Lemma sc_reduce_correct x :
 *   x < 2^512 -> sc_reduce x = x mod L.
 *
 * Note: It's likely we need only one conditional subtraction here, for the
 * same reason only one conditional subtraction is needed for P-256 Barrett
 * reduction, but this needs further investigation to be certain and this
 * routine is not performance-critical.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  [w17:w16]: a, number to be reduced (a < 2^510)
 * @param[in]  [w15:w14]: mu = floor(2^512 / L) (precomputed constant)
 * @param[in]  MOD: L, modulus
 * @param[in]  w31: all-zero
 * @param[out] w18: c, result = a mod L
 *
 * clobbered registers: w10 to w13, w18
 * clobbered flag groups: FG0
 */
.globl sc_reduce
sc_reduce:
  /* First, compute q3 = (x * mu) >> 512.

     Note: As described in HAC, we can probably optimize this by ignoring some
     of the lower partial products of (x * mu), since only the high bits are used.
     However, this optimization increases the possible error of the estimated
     quotient q3, and ensuring it is used safely requires careful analysis.
     Since this routine is not performance-critical, we compute the full
     product here to be safe.

     Since x has 512 bits and mu has 260 bits, rounding up to the nearest
     64-bit limbs gives us a 512x320-bit multiplication. */

  /* Update the accumulator to hold the carry from the lower 512 bits of the
     product. The results from this part are stored in w13 but discarded. */
  bn.mulqacc.z          w14.0, w16.0, 0
  bn.mulqacc            w14.0, w16.1, 64
  bn.mulqacc.so  w13.L, w14.1, w16.0, 64
  bn.mulqacc            w14.0, w16.2, 0
  bn.mulqacc            w14.1, w16.1, 0
  bn.mulqacc            w14.2, w16.0, 0
  bn.mulqacc            w14.0, w16.3, 64
  bn.mulqacc            w14.1, w16.2, 64
  bn.mulqacc            w14.2, w16.1, 64
  bn.mulqacc.so  w13.U, w14.3, w16.0, 64
  bn.mulqacc            w14.0, w17.0, 0
  bn.mulqacc            w14.1, w16.3, 0
  bn.mulqacc            w14.2, w16.2, 0
  bn.mulqacc            w14.3, w16.1, 0
  bn.mulqacc            w15.0, w16.0, 0
  bn.mulqacc            w14.0, w17.1, 64
  bn.mulqacc            w14.1, w17.0, 64
  bn.mulqacc            w14.2, w16.3, 64
  bn.mulqacc            w14.3, w16.2, 64
  bn.mulqacc.so  w13.L, w15.0, w16.1, 64
  bn.mulqacc            w14.0, w17.2, 0
  bn.mulqacc            w14.1, w17.1, 0
  bn.mulqacc            w14.2, w17.0, 0
  bn.mulqacc            w14.3, w16.3, 0
  bn.mulqacc            w15.0, w16.2, 0
  bn.mulqacc            w14.0, w17.3, 64
  bn.mulqacc            w14.1, w17.2, 64
  bn.mulqacc            w14.2, w17.1, 64
  bn.mulqacc            w14.3, w17.0, 64
  bn.mulqacc.so  w13.U, w15.0, w16.3, 64

  /* Finish computing the product (x * mu), and store the high bits.
       [w13:w12] <= (x * mu) >> 512 = q3 */
  bn.mulqacc            w14.1, w17.3, 0
  bn.mulqacc            w14.2, w17.2, 0
  bn.mulqacc            w14.3, w17.1, 0
  bn.mulqacc            w15.0, w17.0, 0
  bn.mulqacc            w14.2, w17.3, 64
  bn.mulqacc            w14.3, w17.2, 64
  bn.mulqacc.so  w12.L, w15.0, w17.1, 64
  bn.mulqacc            w14.3, w17.3, 0
  bn.mulqacc            w15.0, w17.2, 0
  bn.mulqacc.so  w12.U, w15.0, w17.3, 64
  bn.mulqacc.wo    w13, w31.0, w31.0, 0

  /* Load L from the MOD register.
       w11 <= WSR[0x0] = MOD = L */
  bn.wsrr  w11, MOD

  /* Compute the value r2 = (q3 * L) mod 2^256. Since q3 has 260 bits and L has
     253, we use a 320x256-bit multiplication, but we stop after the lowest 256
     bits of the product are computed.
       w10 <= ([w13:w12] * w11) mod 2^256 = (q3 * L) mod 2^256 = r2 mod 2^256 */
  bn.mulqacc.z          w12.0, w11.0, 0
  bn.mulqacc            w12.0, w11.1, 64
  bn.mulqacc.so  w10.L, w12.1, w11.0, 64
  bn.mulqacc            w12.0, w11.2, 0
  bn.mulqacc            w12.1, w11.1, 0
  bn.mulqacc            w12.2, w11.0, 0
  bn.mulqacc            w12.0, w11.3, 64
  bn.mulqacc            w12.1, w11.2, 64
  bn.mulqacc            w12.2, w11.1, 64
  bn.mulqacc.so  w10.U, w12.3, w11.0, 64

  /* Compute r = (x - r2) mod 2^512.

     Note that the conditional addition in HACS is consistent with the
     default behavior of subtraction underflow in OTBN, so there is nothing
     extra to do here. Additionally, because we know that (x - r2) < 2^256, it
     holds that:
       r = (x - r2) mod 2^512 = (x - r2) mod 2^256
         = (x mod 2^256 - r2 mod 2^256) mod 2^256. */

  /* w18 <= (x mod 2^256 - r2 mod 2^256) mod 2^256 = r */
  bn.sub  w18, w16, w10

  /* Finally, two conditional subtractions to correct potential error. We can't
     use addm for the first subtraction because it requires the sum to be less
     than 2*L. */

  /* First conditional subtraction: subtract L and then add it back if the
     borrow flag is set (indicating underflow).
       w18 <= w18 < L ? w18 : w18 - L */
  bn.sub  w18, w18, w11
  bn.sel  w10, w11, w31, C
  bn.add  w18, w18, w10

  /* Second conditional subtraction can simply use add-modulo.
       w18 <= w18 < L ? w18 : w18 - L = x mod L */
  bn.addm w18, w18, w31

  ret

/**
 * Multiply two numbers and reduce modulo L.
 *
 * Returns c = (a * b) mod L.
 *
 * The operands a and b need to fit in 256 bits, but need not be fully reduced
 * modulo L.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w21: a, first operand
 * @param[in]  w22: b, second operand
 * @param[in]  [w15:w14]: mu = floor(2^512 / L) (precomputed constant)
 * @param[in]  MOD: L, modulus
 * @param[in]  w31: all-zero
 * @param[out] w18: c, result = (a * b) mod L
 *
 * clobbered registers: w10 to w13, w16 to w18
 * clobbered flag groups: FG0
 */
.globl sc_mul
sc_mul:
  /* Compute the raw 512-bit product.
     [w17:w16] <= a * b */
  bn.mulqacc.z          w21.0, w22.0, 0
  bn.mulqacc            w21.0, w22.1, 64
  bn.mulqacc.so  w16.L, w21.1, w22.0, 64
  bn.mulqacc            w21.0, w22.2, 0
  bn.mulqacc            w21.1, w22.1, 0
  bn.mulqacc            w21.2, w22.0, 0
  bn.mulqacc            w21.0, w22.3, 64
  bn.mulqacc            w21.1, w22.2, 64
  bn.mulqacc            w21.2, w22.1, 64
  bn.mulqacc.so  w16.U, w21.3, w22.0, 64
  bn.mulqacc            w21.1, w22.3, 0
  bn.mulqacc            w21.2, w22.2, 0
  bn.mulqacc            w21.3, w22.1, 0
  bn.mulqacc            w21.2, w22.3, 64
  bn.mulqacc            w21.3, w22.2, 64
  bn.mulqacc.wo    w17, w21.3, w22.3, 128

  /* Reduce modulo L.
       w18 <= (a * b) mod L */
  jal  x1, sc_reduce

  ret

.data

/* Modulus L = 2^252+27742317777372353535851937790883648493 */
.balign 32
ed25519_scalar_L:
  .word 0x5cf5d3ed
  .word 0x5812631a
  .word 0xa2f79cd6
  .word 0x14def9de
  .word 0x00000000
  .word 0x00000000
  .word 0x00000000
  .word 0x10000000

/* Lower half of the precomputed constant mu = floor(2^512 / L) */
.balign 32
ed25519_scalar_mu_low:
  .word 0x0a2c131b
  .word 0xed9ce5a3
  .word 0x086329a7
  .word 0x2106215d
  .word 0xffffffeb
  .word 0xffffffff
  .word 0xffffffff
  .word 0xffffffff
