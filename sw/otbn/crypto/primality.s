/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl miller_rabin

/* The following subroutines are intended to be internal, but are exposed for
   testing and SCA purposes. */
.globl test_witness

/**
 * Performs the Miller-Rabin primality test.
 *
 * Returns r = 2^256-1 if w is probably prime, 0 if w is composite.
 *
 * This routine runs up to `t` rounds of Miller-Rabin primality checks, exiting
 * early if any check fails (proving w is composite). If `t` rounds succeed,
 * then we declare `w` "probably prime". The exact probability depends on `t`
 * and the size of `w`. For more algorithmic details, see
 * `test_witness`.
 *
 * Requires that the candidate prime w is exactly 2^(n*256) bits:
 *  2^(n*256 - 1) <= w < 2^(n*256)
 * ... and that w is odd.
 *
 * Expects the Montgomery constants for w to be precomputed before entry. None
 * of the input buffers may overlap in DMEM. This routine runs in constant time
 * relative to w if w is probably prime.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] x10: t, number of Miller-Rabin rounds (security parameter)
 * @param[in] x14: dptr_b, pointer to temporary working buffer in dmem (n*32 bytes)
 * @param[in] x15: dptr_z, pointer to temporary working buffer in dmem (n*32 bytes)
 * @param[in] x16: dptr_w, pointer to candidate prime w in dmem, w mod 4 = 3
 * @param[in] x17: dptr_m0inv, pointer to Montgomery constant m0' (for w) in dmem
 * @param[in] x18: dptr_rr, pointer to Montgomery constant RR = R^2 mod w in dmem
 * @param[in] x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in] x31: n-1, number of limbs minus 1
 * @param[in] w31: all-zero
 * @param[out] w21: result, 2^256-1 or 0
 *
 * clobbered registers: x2, x3, x5 to x13, x16, x19 to x26,
 *                      w2, w3, w4..w[4+(n-1)], w20 to w30
 * clobbered flag groups: FG0, FG1
 */
miller_rabin:
  /* Initialize w21 (can be any nonzero value with a high Hamming distance from
     the sensitive "w is prime" value). */
  bn.addi   w21, w31, 1

  loop     x10, 6
    /* Check if w21 is 0, meaning we have already found that w is composite.
         FG0.C <= (w21 == 0) ? 0 : 1 */
    bn.cmp   w31, w21

    /* x2 <= CSRs[FG0][0] = FG0.C */
    csrrs    x2, FG0, x0
    andi     x2, x2, 1

    /* Skip the rest of the loop if w is composite (x2 == 0). We can't exit
       loops early in OTBN, but we can jump past the loop body to speed up
       computation. */
    beq      x2, x0, _miller_rabin_loop_end

    /* Call another round.  */
    jal      x1, miller_rabin_round

    /* We jump here if w has already been found to be composite. */
    _miller_rabin_loop_end:
    nop

  ret

/**
 * Performs one round of the Miller-Rabin primality test.
 *
 * Returns r = 2^256-1 if w is possibly prime, 0 if w is composite.
 *
 * This routine generates a random number in the range [2,w-2] and then calls
 * `test_witness` to check if the selected random number is a
 * witness to the primality of `w`. For more algorithmic details, see
 * `test_witness`.
 *
 * Requires that the candidate prime w is exactly 2^(n*256) bits:
 *  2^(n*256 - 1) <= w < 2^(n*256)
 * ... and that w is odd.
 *
 * Expects the Montgomery constants for w to be precomputed before entry. None
 * of the input buffers may overlap in DMEM. This routine runs in constant time
 * relative to w if w is possibly prime.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] x14: dptr_b, pointer to temporary working buffer in dmem (n*32 bytes)
 * @param[in] x15: dptr_z, pointer to temporary working buffer in dmem (n*32 bytes)
 * @param[in] x16: dptr_w, pointer to candidate prime w in dmem, w mod 4 = 3
 * @param[in] x17: dptr_m0inv, pointer to Montgomery constant m0' (for w) in dmem
 * @param[in] x18: dptr_rr, pointer to Montgomery constant RR = R^2 mod w in dmem
 * @param[in] x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in] x31: n-1, number of limbs minus 1
 * @param[in] w31: all-zero
 * @param[out] w21: result, 2^256-1 or 0
 *
 * clobbered registers: x2, x3, x5 to x13, x16, x19 to x26,
 *                      w2, w3, w4..w[4+(n-1)], w20 to w30
 * clobbered flag groups: FG0, FG1
 */
miller_rabin_round:
  /* Generate a new random number to test. We take input from RND but xor with
     URND as an extra protection (since it is fast and can only strengthen the
     randomness.)
       dmem[dptr_b:dptr_b+n*32] <= RND(n*32) ^ URND(n*32) = b */
  li       x23, 23
  addi     x2, x14, 0
  loop     x30, 4
    /* w22 <= URND() */
    bn.wsrr  w22, URND
    /* w23 <= RND() */
    bn.wsrr  w23, RND
    /* w23 <= w22 ^ w23 */
    bn.xor   w23, w22, w23
    /* b[i] <= w23 */
    bn.sid   x23, 0(x2++)

  /* FG0.C <= 1 */
  bn.subi  w22, w31, 1

  /* Check that b < w - 1.
       FG0.C <= b <? w - FG0.C */
  li       x25, 25
  addi     x2, x14, 0
  addi     x3, x16, 0
  loop     x30, 3
    /* w23 <= b[i] */
    bn.lid   x23, 0(x2++)
    /* w25 <= w[i] */
    bn.lid   x25, 0(x3++)
    /* FG0.C <= b[i] - w[i] - FG0.C */
    bn.cmpb  w23, w25

  /* Extract FG0.C into a small register and jump back to the start if it is 0.
       x2 <= CSRs[FG0][0] = FG0.C */
  csrrs    x2, FG0, x0
  andi     x2, x2, 1
  beq      x2, x0, miller_rabin_round

  /* Clear flags and compute the constant 1.
       w21 <= 1
       FG0.C <= 0 */
  bn.addi  w21, w31, 1

  /* Check that 1 < b.
       FG0.C <= 1 <? b */
  addi     x2, x14, 0
  loop     x30, 3
    /* w23 <= b[i] */
    bn.lid   x23, 0(x2++)
    /* FG0.C <= (i = 0 ? 1 : 0) - b[i] - FG0.C */
    bn.cmpb  w21, w23
    /* w21 <= 0 */
    bn.mov   w21, w31

  /* Extract FG0.C into a small register and retry if it is 0.
       x2 <= CSRs[FG0][0] = FG0.C */
  csrrs    x2, FG0, x0
  andi     x2, x2, 1
  beq      x2, x0, miller_rabin_round

  /* Check if b is a witness to primality for w (tail-call).
       w21 <= all 1s if w is possibly prime, otherwise 0 */
  jal      x0, test_witness


/**
 * Tests one potential witness for the Miller-Rabin primality test.
 *
 * Returns r = 2^256-1 if w is possibly prime, 0 if w is composite.
 *
 * Corresponds to the loop body of Algorithm 4.24 of the Handbook of Applied
 * Cryptography or section B.3.1 of FIPS 186-5. The full algorithm as described
 * by FIPS 186-5 is reproduced here for reference:
 *   1. Let a be the largest integer such that 2^a divides w-1.
 *   2. m = (w-1) / 2^a
 *   3. wlen = len (w).
 *   4. For i = 1 to iterations do
 *     4.1 Obtain a string b of wlen bits from a DRBG. Convert b to an integer
 *     using the algorithm in B.2.1.
 *     4.2 If ((b <= 1) or (b >= w-1)), then go to step 4.1.
 *     4.3 z = b^m mod w.
 *     4.4 If ((z = 1) or (z = w - 1)), then go to step 4.7.
 *     4.5 For j = 1 to a - 1 do.
 *       4.5.1 z = z^2 mod w.
 *       4.5.2 If (z = w - 1), then go to step 4.7.
 *       4.5.3 If (z = 1), then go to step 4.6.
 *     4.6 Return COMPOSITE.
 *     4.7 Continue.
 *   5. Return PROBABLY PRIME.
 *
 * If we specialize to the case that w mod 4 = 3, the routine becomes much
 * simpler and easier to make constant-time, because a in step 1 is always 1.
 * In pseudocode, the modified version of steps 4.3 through 4.7 is:
 *   4.3 Compute z = b^((w-1)/2) mod w.
 *   4.4 If ((z = 1) or (z = w - 1)), then go to step 4.7.
 *   4.5 No-op.
 *   4.6 Return COMPOSITE.
 *   4.7 Continue.
 *
 * Expects the Montgomery constants for w to be precomputed before entry. For
 * this routine, R = 2^(n*256) and R/2 < w < R. None of the input buffers may
 * overlap in DMEM. This routine runs in constant time relative to w if w is
 * possibly prime.
 *
 * This routine is constant-time relative to w if w is possibly prime.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] x14: dptr_b, pointer to randomly-generated witness to use for testing
 * @param[in] x15: dptr_z, pointer to temporary working buffer in dmem (n*32 bytes)
 * @param[in] x16: dptr_w, pointer to candidate prime w in dmem, w mod 4 = 3
 * @param[in] x17: dptr_m0inv, pointer to Montgomery constant m0' (for w) in dmem
 * @param[in] x18: dptr_rr, pointer to Montgomery constant RR = R^2 mod w in dmem
 * @param[in] x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in] x31: n-1, number of limbs minus 1
 * @param[in] w31: all-zero
 * @param[out] w21: result, 2^256-1 or 0
 *
 * clobbered registers: x2, x3, x5 to x13, x16, x19 to x26,
 *                      w2, w3, w4..w[4+(n-1)], w20 to w30
 * clobbered flag groups: FG0, FG1
 */
test_witness:
  /* Initialize constants for montgomery multiplication. */
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  /* Convert the witness to Montgomery form.
       dmem[dptr_b:dptr_b+n*32] <= montmul(b, RR) = (b * R) mod w */
  addi      x19, x14, 0
  addi      x20, x18, 0
  jal       x1, montmul
  addi      x21, x14, 0
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* Initialize wide-register pointers. */
  li        x23, 23
  li        x25, 25

  /* Ensure the last 3 bits of the candidate prime are set so that w mod 4 = 3.
     This is a precondition of the subroutine, but re-setting the bits here
     provides further protection from e.g. fault injection attacks. */
  bn.lid    x25, 0(x16)
  bn.addi   w23, w31, 3
  bn.or    w25, w25, w23
  bn.sid    x25, 0(x16)

  /* Clear carry flag.
       FG0.C <= 0 */
  bn.sub    w31, w31, w31

  /* Initialize work buffer to (R - w) mod w (1 in Montgomery form).
       dmem[dptr_z:dptr_z+n*32] <= (0 - w) mod R = R - w = R mod w */
  addi      x20, x16, 0
  addi      x21, x15, 0
  loop      x30, 3
    bn.lid    x23, 0(x20++)
    bn.subb   w23, w31, w23
    bn.sid    x23, 0(x21++)

  /* Initialize loop counter and high limb.
       x26 <= n - 1
       w20 <= 0 */
  addi      x26, x31, 0
  bn.sub    w20, w20, w20

  /* Perform modular exponentiation to compute b^((w-1)/2).

     Loop through the limbs, most significant first, then iterate through each
     bit of each limb.

     Loop invariants (i=n-1 to 0):
       x15 = dptr_z
       x16 = dptr_w
       x26 = i
       w20 = w[i+1] (or 0 if i=n-1)
       dmem[dptr_z:dptr_z+n*32] <= (b^((w - 1) >> (i*256)) * R) mod w */
  loop    x30, 27
    /* Get the ith limb of w.
         w25 <= dmem[dptr_w + (i << 5)] = w[i] */
    slli      x13, x26, 5
    add       x13, x13, x16
    bn.lid    x25, 0(x13)

    /* Get limb i of ((w-1) / 2). Since we know w is odd, we can simply
       concatenate with the limb above and shift right by 1.
         w22 <= (w20[0] << 255) | (w[i] >> 1) = (w >> 1)[i] */
    bn.rshi   w22, w20, w25 >> 1

    /* Save the ith limb for the next iteration.
         w20 <= w[i] */
    bn.mov    w20, w25

   /* Loop through the bits of this limb and multiply/accumulate. */
    loopi   256, 19
      /* Perform the next squaring step of modular exponentiation.
           w4..w[4+(n-1)] = montmul(z, z) */
      addi      x19, x15, 0
      addi      x20, x15, 0
      jal       x1, montmul

      /* Store squaring result in work buffer.
           dmem[dptr_z:dptr_z+n*32] <= w4..w[4+(n-1)] */
      addi      x21, x15, 0
      loop      x30, 2
        bn.sid    x8, 0(x21++)
        addi      x8, x8, 1

      /* Perform the next multiplication step of modular exponentiation.
           w4..w[4+(n-1)] = montmul(z, b) */
      addi      x19, x14, 0
      addi      x20, x15, 0
      jal       x1, montmul

      /* Shift the exponent and update flags; FG0.C will now be the next bit of
         the exponent.
           w22 <= (w22 << 1) mod 2^256
           FG0.C <= w22[255] */
      bn.add    w22, w22, w22

      /* Select either squared or squared+multiplied result based on FG0.C.
           dmem[dptr_z:dptr_z+n*32] <=
             FG0.C ? w4..w[4+(n-1)] : dmem[dptr_z:dptr_z+n*32] */
      addi      x2, x15, 0
      li        x8, 4
      loop      x30, 4
        /* w23 <= dmem[dptr_z+i*32] */
        bn.lid    x23, 0(x2)
        /* w25 <= w[4+i] */
        bn.movr   x25, x8++
        /* w23 = FG0.C ? w[4+i] : dmem[dptr_z+i*32] */
        bn.sel    w23, w25, w23, FG0.C
        /* dmem[dptr_z+i*32] <= w23 */
        bn.sid    x23, 0(x2++)

      /* End of inner loop. */
      nop

    /* Update loop counter.
         x26 <= x26 - 1 = i - 1 */
    li        x3, 1
    sub       x26, x26, x3
    /* End of outer loop. */

  /* Fully reduce mod w. The `montmul` routine does not guarantee that the
     result is < w, only < R.
       dmem[dptr_z:dptr_z+n*32] <= dmem[dptr_z:dptr_z+n*32] mod w */
  jal       x1, reduce_modw

  /* Check if the intermediate result represents 1 in Montgomery form.
       w22 <= all 1s if dmem[x15:x15+n*32] is R mod w, otherwise 0 */
  jal      x1, is_mont1
  bn.mov   w22, w26

  /* Check if the work buffer is (-R) mod w, which is the Montgomery form
     representation of (-1) mod w = w - 1.
        w26 <= all 1s if dmem[x15:x15+n*32] is (-R) mod w, otherwise 0 */
  jal      x1, is_mont_minus1

  /* If either check returned all-ones, then the input is possibly prime. */
  bn.or    w21, w26, w22

  /* TODO: add an FI check here to ensure we completed all loop iterations if
     the result register is all 1s. */

  ret

/**
 * Fully reduce modulo a candidate prime w.
 *
 * Returns x mod w = (x - w) if x >= w, otherwise x.
 *
 * This routine requires that R/2 < w < R and that R = 2^(n*256). Since x < R,
 * at most one conditional subtraction is required to reduce.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] x15: dptr_x, pointer to input buffer x in dmem
 * @param[in] x16: dptr_m, pointer to modulus m in dmem
 * @param[in] x23: 23, constant
 * @param[in] x25: 25, constant
 * @param[in] x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in] w31: all-zero
 *
 * clobbered registers: x2, x3, w23, w25
 * clobbered flag groups: FG0, FG1
 */
reduce_modw:
  /* Clear flags in group 1. */
  bn.sub    w31, w31, w31, FG1

  /* Compare input to modulus.
       FG1.C <= if x < w then 1 else 0 */
  addi      x2, x15, 0
  addi      x3, x16, 0
  loop      x30, 3
    bn.lid    x23, 0(x2++)
    bn.lid    x25, 0(x3++)
    bn.cmpb   w23, w25, FG1

  /* Clear flags in group 0. */
  bn.sub    w31, w31, w31

  /* Conditional subtraction.
       dmem[dptr_x:dptr_x+n*32] <= FG1.C ? x : x - w */
  addi      x2, x15, 0
  addi      x3, x16, 0
  loop      x30, 5
    bn.lid    x23, 0(x2)
    bn.lid    x25, 0(x3++)
    bn.subb   w25, w23, w25
    bn.sel    w23, w23, w25, FG1.C
    bn.sid    x23, 0(x2++)

  ret

/**
 * Determine if a number represents 1 in Montgomery form.
 *
 * Returns 2^256 - 1 if (x == R mod w), otherwise 0
 *
 * This routine requires that R/2 < w < R and that R = 2^(n*256). With that
 * assumption, we know that R mod w = R - w; if x is 1, then (w + x) mod R will
 * be zero.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] x15: dptr_x, pointer to input buffer x in dmem
 * @param[in] x16: dptr_m, pointer to modulus m in dmem
 * @param[in] x23: 23, constant
 * @param[in] x25: 25, constant
 * @param[in] x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in] w31: all-zero
 * @param[out] w26: result, 2^256-1 or 0
 *
 * clobbered registers: x2, x3, w23, w25, w26
 * clobbered flag groups: FG0
 */
is_mont1:
  /* Clear flags and initialize return value.
       w26 <= 2^256 - 1
       FG0.C <= 0 */
  bn.sub   w26, w26, w26
  bn.not   w26, w26

  /* Compute whether (w + x) mod R is all-zero. */
  addi     x2, x15, 0
  addi     x3, x16, 0
  loop     x30, 4
    /* w23 <= x[i] */
    bn.lid   x23, 0(x2++)
    /* w25 <= w[i] */
    bn.lid   x25, 0(x3++)
    /* w25 <= (x + w)[i]
       FG0.C <= (x[i] + w[i] + FG0.C) >? 2^256
       FG0.Z <= (x + w)[i] =? 0 */
    bn.addc  w25, w23, w25
    /* w26 <= FG0.Z ? w26 : w31 */
    bn.sel   w26, w26, w31, FG0.Z

  /* Now, the mask will be all 1s if (w + x) mod R == 0 and zero otherwise. */
  ret

/**
 * Determine if a number represents (-1) in Montgomery form.
 *
 * Returns 2^256 - 1 if (x == (-R) mod w), otherwise 0
 *
 * This routine requires that R/2 < w < R and that R = 2^(n*256). We check if
 * x represents -1 by negating the number mod w in-place, checking if it is 1,
 * and then negating back. Because of the method used for negation, this
 * routine requires that x is fully reduced (x < w).
 *
 * TODO (optimization): precompute (2w - R), which is the only possible value
 * equivalent to (-R mod w) in the RSA context because of the minimum value of
 * prime candidates (sqrt(2) * (R / 2)). Then we could simply compare directly
 * here, and also avoid the need for full modular reduction in the main loop.
 * However, it would require DMEM space and make the implementation subtly more
 * specialized and sensitive to the range of w (for some w, 3w - R could also
 * be equivalent to w - 1).
 *
 * WARNING: this routine clobbers its input in DMEM (dmem[dptr_x..dptr_x+n*32]).
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] x15: dptr_x, pointer to input buffer x in dmem
 * @param[in] x16: dptr_m, pointer to modulus m in dmem
 * @param[in] x23: 23, constant
 * @param[in] x25: 25, constant
 * @param[in] x30: n, number of limbs for all bignums (wlen / 256; n <= 16)
 * @param[in] w31: all-zero
 * @param[out] w26: result, 2^256-1 or 0
 *
 * clobbered registers: x2, x3, w23, w25, w26
 * clobbered flag groups: FG0
 */
is_mont_minus1:
  /* Clear flags. */
  bn.sub   w31, w31, w31

  /* Negate the input in-place.
       dmem[dptr_x:dptr_x+n*32] <= w - dmem[dptr_x:dptr_x+n*32] */
  addi     x2, x15, 0
  addi     x3, x16, 0
  loop     x30, 4
    /* w23 <= x[i] */
    bn.lid   x23, 0(x2)
    /* w25 <= w[i] */
    bn.lid   x25, 0(x3++)
    /* w23 <= w[i] - out[i] - FG0.C */
    bn.subb  w23, w25, w23
    /* out[i] <= w23 */
    bn.sid   x23, 0(x2++)

  /* Check if the input is 1.
       w26 <= all 1s if dmem[dptr_x:dptr_x+n*32] == (-R) mod w, otherwise 0 */
  jal      x1, is_mont1

  ret
