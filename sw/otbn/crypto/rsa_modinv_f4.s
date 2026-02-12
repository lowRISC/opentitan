/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.text
.globl modinv_f4

/**
 * Compute the inverse of 65537 modulo a given number.
 *
 * Returns d such that (d*65537) = 1 mod m and 0 <= d < m.
 *
 * Requires that m is nonzero, and that GCD(m, 65537) = 1.
 *
 * This is a specialized version of binary extended GCD, as described in HAC
 * Algorithm 14.61 and implemented in constant time in BoringSSL here:
 *   https://boringssl.googlesource.com/boringssl/+/dcabfe2d8940529a69e007660fa7bf6c15954ecc/crypto/fipsmodule/bn/gcd_extra.c#170
 *
 * BoringSSL's version includes a few improvements beyond being constant-time,
 * such as avoiding signed integers. This modified algorithm has also been
 * proven mathematically correct in Coq, see:
 *   https://github.com/mit-plv/fiat-crypto/pull/333
 *
 * In pseudocode,the BoringSSL algorithm is:
 *   A, B, C, D = 1, 0, 0, 1
 *   u = x
 *   v = y
 *   // Loop invariants:
 *   //   A*x - B*y = u
 *   //   D*y - C*x = v
 *   //   gcd(u, v) = gcd(x, y)
 *   //   bitlen(u) + bitlen(v) <= i
 *   //   0 < u <= x
 *   //   0 <= v <= y
 *   //   0 <= A, C < y
 *   //   0 <= B, D <= x
 *   for i=bitlen(x) + bitlen(y)..1:
 *     if u and v both odd:
 *       if v < u:
 *         u = u - v
 *         A = (A + C) mod y
 *         B = (B + D) mod x
 *       else:
 *         v = v - u
 *         C = (A + C) mod y
 *         D = (B + D) mod x
 *     // At this point, the invariant holds and >= 1 of u and v is even
 *     if u is even:
 *       u >>= 1
 *       if (A[0] | B[0]):
 *         A = (A + y) / 2
 *         B = (B + x) / 2
 *       else:
 *         A >>= 1
 *         B >>= 1
 *     if v is even:
 *       v >>= 1
 *       if (C[0] | D[0]):
 *         C = (C + x) / 2
 *         D = (D + y) / 2
 *       else:
 *         C >>= 1
 *         D >>= 1
 *    // End of loop. Guarantees the invariant plus u = gcd(x,y).
 *
 * As described in HAC note 14.64, this algorithm computes a modular inverse
 * when gcd(x,y) = 1. Specifically, at termination, A = x^-1 mod y because:
 *   (A*x) mod y = (A*x - B*y) mod y = u mod y = 1
 *
 * Of course, all the if statements are implemented with constant-time selects.
 *
 * The fully specialized and constant-time version of the pseudocode is:
 *   A, C = 1, 0
 *   u = 65537
 *   v = m
 *   // Loop invariants:
 *   //   A*x - B*y = u
 *   //   D*y - C*x = v
 *   //   gcd(u, v) = gcd(x, y)
 *   //   bitlen(u) + bitlen(v) <= i
 *   //   gcd(u, v) = 1
 *   //   bitlen(u) + bitlen(v) <= i
 *   //   0 < u <= 65537
 *   //   0 <= v <= m
 *   //   0 <= A, C < m
 *   //   0 <= B,D < 65537
 *   for i=(bitlen(m) + bitlen(65537))..1:
 *     both_odd = u[0] & v[0]
 *     v_lt_u = v < u
 *     u = u - ((both_odd && v_lt_u) ? v : 0)
 *     v = v - ((both_odd && !v_lt_u) ? u : 0)
 *     ac = (A + C) mod m
 *     A = (both_odd && v_lt_u) ? ac : A
 *     C = (both_odd && !v_lt_u) ? ac : C
 *     bd = (B + D) mod 65537
 *     B = (both_odd && v_lt_u) ? bd : B
 *     D = (both_odd && !v_lt_u) ? bd : D
 *     u_even = !u[0]
 *     a_or_b_odd = A[0] | B[0]
 *     u = u_even ? u >> 1 : u
 *     A = (u_even && a_or_b_odd) ? (A + m) : A
 *     A = u_even ? (A >> 1) : A
 *     B = (u_even && a_or_b_odd) ? (B + 65537) : B
 *     B = u_even ? (B >> 1) : B
 *     v_even = !v[0]
 *     c_or_d_odd = C[0] | D[0]
 *     v = v_even ? v >> 1 : v
 *     C = (v_even && c_or_d_odd) ? (C + m) : C
 *     C = v_even ? (C >> 1) : C
 *     D = (u_even && c_or_d_odd) ? (D + 65537) : D
 *     D = u_even ? (D >> 1) : D
 *   if u != 1:
 *     FAIL("Not invertible")
 *   return A
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x12: dptr_m, pointer to modulus m in DMEM (n limbs)
 * @param[in]  x13: dptr_A, pointer to result buffer in DMEM (n limbs)
 * @param[in]  x14: dptr_C, pointer to a temporary buffer in DMEM (n limbs)
 * @param[in]  x15: dptr_v, pointer to a temporary buffer in DMEM (n limbs)
 * @param[in]  x20: 20, constant
 * @param[in]  x21: 21, constant
 * @param[in]  x30: nlen, number of 256-bit limbs for modulus m and result d
 * @param[in]  w31: all-zero
 * @param[out] dmem[dptr_A..dptr_A+(plen*32)]: result, modular inverse d
 *
 * clobbered registers: MOD, x2 to x4, x31, w20 to w28
 * clobbered flag groups: FG0, FG1
 */
modinv_f4:
  /* Zero the intermediate buffers.
       dmem[dptr_A..dptr_A+(nlen*32)] <= 0
       dmem[dptr_C..dptr_C+(nlen*32)] <= 0 */
  li       x2, 31
  addi     x3, x13, 0
  addi     x4, x14, 0
  loop     x30, 2
    bn.sid   x2, 0(x3++)
    bn.sid   x2, 0(x4++)

  /* Set the lowest limb of A to 1.
       dmem[dptr_A] <= 1 */
  bn.addi  w20, w31, 1
  bn.sid   x20, 0(x13)

  /* Initialize B to 0.
       w27 <= 0 */
  bn.mov   w27, w31

  /* Initialize D to 1.
       w28 <= 1 */
  bn.addi  w28, w31, 1

  /* Copy the modulus to the buffer for v.
       dmem[dptr_v..dptr_v+(nlen*32)] <= m */
  addi     x3, x12, 0
  addi     x4, x15, 0
  loop     x30, 2
    bn.lid   x20, 0(x3++)
    bn.sid   x20, 0(x4++)

  /* Initialize u = F4.
       w22 <= (1 << 16) + 1 = 65537 */
  bn.addi  w23, w31, 1
  bn.add   w22, w23, w23 << 16

  /* MOD <= 65537 */
  bn.wsrw  MOD, w22

  /* Calculate number of loop iterations = bitlen(m) + bitlen(65537).
       x31 <= (x30 << 8) + 17 = 256*n + 17 */
  slli     x31, x30, 8
  addi     x31, x31, 17

  /* Main loop. */
  loop     x31, 121
    /* Load the least significant limb of v.
         w20 <= dmem[dptr_v] = v[255:0] */
    bn.lid   x20, 0(x15)

    /* Construct a flag that is 1 if both u and v are odd.
         FG1.L <= (w22 & w20)[0] = u[0] && v[0] */
    bn.and   w20, w22, w20, FG1

    /* Compare u and v.
         FG0.C <= v < u */
    bn.mov   w23, w22
    addi     x2, x15, 0
    loop     x30, 3
      /* w20 <= v[i] */
      bn.lid   x20, 0(x2++)
      /* FG0.C <= v[i] <? w23 + FG0.C */
      bn.cmpb  w20, w23
      /* Higher limbs of u are all zero; set w23 = 0 for next round. */
      bn.mov   w23, w31

    /* Capture FG0.C in a mask.
         w23 <= FG0.C ? 2^256 - 1 : 0 */
    bn.subb  w23, w31, w31

    /* Select a mask that is all 1s if we should subtract v from u.
         w24 <= FG1.L ? w23 : w31 = (u[0] && v[0] && v < u) ? 2^256 - 1 : 0 */
    bn.sel   w24, w23, w31, FG1.L

    /* Select a mask that is all 1s if we should subtract u from v.
         w25 <= FG1.L ? !w23 : w31 = (u[0] && v[0] && u <= v) ? 2^256 - 1 : 0 */
    bn.not   w23, w23
    bn.sel   w25, w23, w31, FG1.L

    /* Conditionally subtract v from u. If we do this subtraction, we know that
       v < u <= 65537, so we can use only one limb of v.
         w22 <= w22 - (dmem[dptr_v] & w24) */
    bn.lid   x20, 0(x15)
    bn.and   w20, w20, w24
    bn.sub   w22, w22, w20

    /* Conditionally subtract u from v.
         dmem[dptr_v..dptr_v+(nlen*32)] <= v - (u & w25) */
    bn.and   w23, w22, w25
    addi     x2, x15, 0
    loop     x30, 4
      /* w20 <= v[i] */
      bn.lid   x20, 0(x2)
      /* w20, FG0.C <= v[i] - w23 - FG0.C */
      bn.subb  w20, w20, w23
      /* v[i] <= w20 */
      bn.sid   x20, 0(x2++)
      /* Higher limbs of u are all zero; set w23 = 0 for next round. */
      bn.mov   w23, w31

    /* Calculate what we should add to B; D if we updated u in the previous
       steps (w24 == 2^256=1), otherwise 0.
         w20 <= (D & w24) */
    bn.and   w20, w28, w24

    /* Calculate what we should add to D; B if we updated v in the previous
       steps (w25 == 2^256=1), otherwise 0.
         w21 <= (B & w25) */
    bn.and   w21, w27, w25

    /* Update B.
         w27 <= (B + (D & w24)) mod 65537 */
    bn.addm  w27, w27, w20

    /* Update D.
         w27 <= (D + (B & w25)) mod 65537 */
    bn.addm  w28, w28, w21

    /* Clear flags for both groups. */
    bn.sub   w31, w31, w31, FG0
    bn.sub   w31, w31, w31, FG1

    /* Compare (A + C) to m.
         FG1.C <= A + C < m */
    addi     x2, x12, 0
    addi     x3, x13, 0
    addi     x4, x14, 0
    loop     x30, 5
      /* w20 <= A[i] */
      bn.lid   x20, 0(x3++)
      /* w21 <= C[i] */
      bn.lid   x21, 0(x4++)
      /* w23, FG0.C <= A[i] + C[i] + FG0.C */
      bn.addc  w23, w20, w21
      /* w20 <= m[i] */
      bn.lid   x20, 0(x2++)
      /* FG1.C <= w23 <? m[i] + FG1.C */
      bn.cmpb  w23, w20, FG1

    /* The modulus needs to be subtracted (w26 = all 1s) in two cases:
         1. FG1.C = 0, the last word addition did not underlow: A + C > m.
         2. FG0.C = 1, the last word addition has overflowed:   A + C > m. */
    bn.not   w23, w31
    bn.sel   w26, w31, w23, FG1.C
    bn.sel   w26, w23, w26, FG0.C

    /* Clear flags for both groups. */
    bn.sub   w31, w31, w31, FG0
    bn.sub   w31, w31, w31, FG1

    /* Update A if we updated u in the previous steps (w24 == 2^256-1). We
       additionally subtract the modulus if *both* w24,w26 == 2^256-1.
         dmem[dptr_A..dptr_A+(nlen*32)] <= (w24 == 2^256-1) ? (A + C) mod m : A */
    addi     x2, x12, 0
    addi     x3, x13, 0
    addi     x4, x14, 0
    loop     x30, 9
      /* w20 <= A[i] */
      bn.lid   x20, 0(x3)
      /* w21 <= C[i] */
      bn.lid   x21, 0(x4++)
      /* w21 <= C[i] & w24 */
      bn.and   w21, w21, w24
      /* w20, FG0.C <= w20 + w21 + FG0.C */
      bn.addc  w20, w20, w21
      /* w21 <= m[i] */
      bn.lid   x21, 0(x2++)
      /* w21 <= m[i] & w24 */
      bn.and   w21, w21, w24
      /* w21 <= m[i] & w24 & w26 */
      bn.and   w21, w21, w26
      /* w20, FG1.C <= w20 - w21 - FG1.C  */
      bn.subb  w20, w20, w21, FG1
      /* A[i] <= w20 */
      bn.sid   x20, 0(x3++)

    /* Update C if we updated v in the previous steps (w25 == 2^256-1). We
       additionally subtract the modulus if *both* w25,w26 == 2^256-1.
         dmem[dptr_C..dptr_C+(nlen*32)] <= (w25 == 2^256-1) ? (A + C) mod m : C */
    addi     x2, x12, 0
    addi     x3, x13, 0
    addi     x4, x14, 0
    loop     x30, 9
      /* w20 <= C[i] */
      bn.lid   x20, 0(x4)
      /* w21 <= A[i] */
      bn.lid   x21, 0(x3++)
      /* w21 <= A[i] & w25 */
      bn.and   w21, w21, w25
      /* w20, FG0.C <= w20 + w21 + FG0.C */
      bn.addc  w20, w20, w21
      /* w21 <= m[i] */
      bn.lid   x21, 0(x2++)
      /* w21 <= m[i] & w25 */
      bn.and   w21, w21, w25
      /* w21 <= m[i] & w25 & w26 */
      bn.and   w21, w21, w26
      /* w20, FG1.C <= w20 - w21 - FG1.C  */
      bn.subb  w20, w20, w21, FG1
      /* C[i] <= w20 */
      bn.sid   x20, 0(x4++)

    /* Get a flag that is set if u is odd.
         FG1.L <= u[0] */
    bn.or    w22, w22, w31, FG1

    /* Update u if it is even.
         w22 <= FG1.L ? w22 : w22 >> 1 */
    bn.rshi  w23, w31, w22 >> 1
    bn.sel   w22, w22, w23, FG1.L

    /* Create an all-ones mask.
         w23 <= 2^256 - 1 */
    bn.not   w23, w31

    /* Get a flag that is set if A or B is odd.
         FG0.L <= A[0] | B[0] */
    bn.lid   x20, 0(x13)
    bn.or    w20, w20, w27

    /* Select a mask for adding moduli to A and B (should do this if u is even
       and at least one of A and B is odd).
         w23 <= (!FG1.L && FG0.L) ? 2^256 - 1 : 0 */
    bn.sel   w23, w31, w23, FG1.L
    bn.sel   w23, w23, w31, FG0.L

    /* Conditionally add to B.
         w27 <= B + (65537 & w23) */
    bn.wsrr  w24, MOD
    bn.and   w24, w24, w23
    bn.add   w27, w27, w24

    /* Shift B if u is even.
         w27 <= FG1.L ? B : B >> 1 */
    bn.rshi  w24, w31, w27 >> 1
    bn.sel   w27, w27, w24, FG1.L

    /* Clear flags for group 0. */
    bn.sub   w31, w31, w31

    /* Conditionally add m to A.
         dmem[dptr_A..dptr_A+(nlen*32)] <= (!u[0] && (A[0] | B[0])) ? A + m : A */
    addi     x2, x12, 0
    addi     x3, x13, 0
    loop     x30, 5
      /* w20 <= A[i] */
      bn.lid   x20, 0(x3)
      /* w21 <= m[i] */
      bn.lid   x21, 0(x2++)
      /* w21 <= m[i] & w23 */
      bn.and   w21, w21, w23
      /* w20, FG0.C <= A[i] + (m[i] & w23) + FG0.C */
      bn.addc  w20, w20, w21
      /* A[i] <= w20 */
      bn.sid   x20, 0(x3++)

    /* Capture the final carry bit in a register to use as the MSB for the
       shift. */
    bn.addc  w23, w31, w31

    /* Shift A to the right 1 if FG1.L is unset.
         dmem[dptr_A..dptr_A+(nlen*32)] <= FG1.L ? A : A >> 1 */
    addi     x3, x13, 0
    jal      x1, bignum_rshift1_if_not_fg1L

    /* Get a flag that is set if v is odd.
         FG1.L <= v[0] */
    bn.lid   x20, 0(x15)
    bn.or    w20, w20, w31, FG1

    /* Shift v to the right 1 if FG1.L is unset.
         dmem[dptr_v..dptr_v+(nlen*32)] <= FG1.L ? v : v >> 1 */
    addi     x3, x15, 0
    bn.mov   w23, w31
    jal      x1, bignum_rshift1_if_not_fg1L

    /* Create an all-ones mask.
         w23 <= 2^256 - 1 */
    bn.not   w23, w31

    /* Get a flag that is set if C or D is odd.
         FG0.L <= C[0] | D[0] */
    bn.lid   x20, 0(x14)
    bn.or    w20, w20, w28

    /* Select a mask for adding moduli to C and D (should do this if v is even
       and at least one of C and D is odd).
         w23 <= (!FG1.L && FG0.L) ? 2^256 - 1 : 0 */
    bn.sel   w23, w31, w23, FG1.L
    bn.sel   w23, w23, w31, FG0.L

    /* Conditionally add to D.
         w28 <= D + (65537 & w23) */
    bn.wsrr  w24, MOD
    bn.and   w24, w24, w23
    bn.add   w28, w28, w24

    /* Shift D if u is even.
         w28 <= FG1.L ? D : D >> 1 */
    bn.rshi  w24, w31, w28 >> 1
    bn.sel   w28, w28, w24, FG1.L

    /* Clear flags for group 0. */
    bn.sub   w31, w31, w31

    /* Conditionally add m to C.
         dmem[dptr_C..dptr_C+(nlen*32)] <= (!v[0] && (C[0] | D[0])) ? C + m : C */
    addi     x2, x12, 0
    addi     x3, x14, 0
    loop     x30, 5
      /* w20 <= C[i] */
      bn.lid   x20, 0(x3)
      /* w21 <= m[i] */
      bn.lid   x21, 0(x2++)
      /* w21 <= m[i] & w23 */
      bn.and   w21, w21, w23
      /* w20, FG0.C <= C[i] + (m[i] & w23) + FG0.C */
      bn.addc  w20, w20, w21
      /* A[i] <= w20 */
      bn.sid   x20, 0(x3++)

    /* Capture the final carry bit in a register to use as the MSB for the
       shift. */
    bn.addc  w23, w31, w31

    /* Shift C to the right 1 if FG1.L is unset.
         dmem[dptr_C..dptr_C+(nlen*32)] <= FG1.L ? C : C >> 1 */
    addi     x3, x14, 0
    jal      x1, bignum_rshift1_if_not_fg1L

    /* End of loop; no-op so we don't end on a jump. */
    nop

  /* FG0.Z <= u == 1 */
  bn.addi    w23, w31, 1
  bn.cmp     w22, w23

  /* Get the FG0.Z flag into a register.
       x2 <= CSRs[FG0] & 8 = FG0.Z << 3 */
  csrrs    x2, FG0, x0
  andi     x2, x2, 8

  /* If the flag is unset (x2 == 0) then u != 1; in this case GCD(65537, m) !=
     1 and the modular inverse cannot be computed. This should never happen
     under normal operation, so panic and abort the program immediately. */
  bne      x2, x0, _modinv_f4_u_ok
  unimp

_modinv_f4_u_ok:
  /* Done; the modular inverse is stored in A. */

  ret

/**
 * Shifts input 1 bit to the right in-place if FG1.L is 0.
 *
 * Returns A' = if FG1.L then A else (msb || A) >> 1.
 *
 * The MSB of the final result will be the LSB of w23.
 *
 * Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]   x3: dptr_A, pointer to input A in DMEM
 * @param[in]  x20: 20, constant
 * @param[in]  x21: 21, constant
 * @param[in]  x30: alen, number of 256-bit limbs for input A
 * @param[in]   w23: value to use as the msb
 * @param[in]   w31: all-zero
 * @param[out] dmem[dptr_A..dptr_A+alen*32]: A', result
 *
 * clobbered registers: x2, x3, x4, w20, w21
 * clobbered flag groups: FG0
 */
bignum_rshift1_if_not_fg1L:
  /* Calculate number of loop iterations for bignum shifts.
       x2 <= n - 1 */
  addi     x2, x0, 1
  sub      x2, x30, x2

  /* Conditionally shift the lower limbs. */
  addi      x4, x3, 32
  loop      x2, 5
    /* w20 <= dmem[x3] = A[i] */
    bn.lid    x20, 0(x3)
    /* w21 <= dmem[x4] = A[i+1] */
    bn.lid    x21, 0(x4++)
    /* w21 <= (A >> 1)[i] */
    bn.rshi   w21, w21, w20 >> 1
    /* w20 <= FG1.L ? w20 : w21 */
    bn.sel    w20, w20, w21, FG1.L
    /* dmem[x3] <= w20 */
    bn.sid    x20, 0(x3++)

  /* Last limb is special because there's no next limb; we use the provided
     input value. */
  bn.lid    x20, 0(x3)
  bn.rshi   w21, w23, w20 >> 1
  bn.sel    w21, w20, w21, FG1.L
  bn.sid    x21, 0(x3)

  ret
