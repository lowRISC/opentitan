/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c
 */


.text
.globl modexp_65537
.globl modexp

/**
 * Precomputation of a constant m0' for Montgomery modular arithmetic
 *
 * Word-wise montgomery modular arithmetic requires a quantity m0' to be
 * precomputed once per modulus M. m0' is the negative of the
 * modular multiplicative inverse of the lowest limb m0 of the modulus M, in
 * the field GF(2^w), where w is the number of bits per limb. w is set to 256
 * in this subroutine.
 *
 * Returns: m0' = -m0^(-1) mod 2^256
 *          with m0 being the lowest limb of the modulus M
 *
 * This subroutine implements the Dusse-Kaliski method for computing the
 * multiplicative modular inverse when the modulus is of the form 2^k.
 * [Dus] DOI https://doi.org/10.1007/3-540-46877-3_21 section 3.2
 *       (Algorithm "Modular Inverse" on p. 235)
 *
 * Flags: When leaving this subroutine, flags of FG0 depend on a
 *        the final subtraction and can be used if needed.
 *        FG0.M, FG0.L, FG0.Z depend directly on the value of the result m0'.
 *        FG0.C is always set.
 *        FG1 is not modified in this subroutine.
 *
 * @param[in]  w28: m0, the lowest 256 bit limb of the modulus M
 * @param[in]  w31: all-zero.
 * @param[out] w29: m0', negative of inverse of m0 in GF(2^256)
 *
 * clobbered registers: w0, w1, w29
 * clobbered flag groups: FG0
 */
d0inv:
  /* w0 keeps track of loop iterations in one-hot encoding, i.e.
     w0 = 2^i in the loop body below and initialized here with w0 = 1
     It is used for both the comparison in step 4 of [Dus] and the
     addition in step 6 of [Dus] */
  bn.xor    w0, w0, w0
  bn.addi   w0, w0, 1

  /* according to [Dus] the result variable y is initialized with 1 */
  /* w29 = y_0 = 1 */
  bn.mov    w29, w0

  /* iterate over all 256 bits of m0.
     i refers to the loop cycle 0..255 in the loop body below. */
  loopi     256, 13

    /* y_i <= m*y_{i-1] */
    bn.mulqacc.z          w28.0, w29.0,  0
    bn.mulqacc            w28.1, w29.0, 64
    bn.mulqacc.so   w1.L, w28.0, w29.1, 64
    bn.mulqacc            w28.2, w29.0,  0
    bn.mulqacc            w28.1, w29.1,  0
    bn.mulqacc            w28.0, w29.2,  0
    bn.mulqacc            w28.3, w29.0, 64
    bn.mulqacc            w28.2, w29.1, 64
    bn.mulqacc            w28.1, w29.2, 64
    bn.mulqacc.so   w1.U, w28.0, w29.3, 64

  /* This checks if w1 = y_i = m0*y_(i-1) < 2^(i-1) mod 2^i
     Due to the mathematical properties it can be shown that y_i at this point,
     is either 1 or (10..0..01)_(i). Therefore, just probing the i_th bit is
     the same as the full compare. */
    bn.and    w1, w1, w0

    /* Compute
       y_i=w29 <= w1=m0*y_(i-1) < 2^(i-1) mod 2^i y_i ? : y_{i-1}+2^i : y_{i-1}
       there cannot be overlaps => or'ing is as good as adding */
    bn.or     w29, w29, w1

    /* double w0 (w0 <= w0 << 1) i.e. w0=2^i */
    bn.add    w0, w0, w0

  /* finally, compute m0' (negative of inverse)
     w29 = m0' = -(m0^-1) mod 2^256 = -y_255 = 0 - y_255 = w31 - w29 */
  bn.sub    w29, w31, w29

  ret

/**
 * Constant time conditional subtraction of modulus from a bigint
 *
 * Returns C <= C-s*M
 *         with C being a bigint of length 256..4096 bit
 *              M being the modulus of length 256..4096 bit
 *              s being a boolean value [0,1]
 *
 * Conditionally subtracts the modulus located in dmem from the bigint
 * located in a buffer in the wide regfile (starting at w5). The subtracted
 * value is seleced when FG1.C equals 1, otherwise the unmodifed value is
 * selected.
 *
 * Note that the interpretation of the subtrahend as a modulus is only
 * contextual. In theory, it can be any bigint. However, the subtrahend is
 * expected in dmem at a location that is reserved for the modulus according
 * to the calling conventions within this library.
 *
 * Flags: When leaving this subroutine, flags of FG0 depend on a
 *        potentially discarded value and therefore are not usable after
 *        return.
 *        FG1 is not modified in this subroutine.
 *
 * @param[in]  [dmem[3]:dmem[0]]: pointer to 1st limb of modulus M
 * @param[in]  w30: N, number of 256 bit limbs in modulus and bigint
 * @param[in]  w31: all-zero
 * @param[in]  FG1.C: s, selection flag
 * @param[out] [w[5+N-1]:w5]: new bigint value
 * @param[in]  FG0.C: needs to be set to 0
 *
 * clobbered registers: x8, x10, x11, x16, w2, w3, w4, w5 to w[5+N-1]
 * clobbered flag groups: FG0
 */
selcxSub:

  /* setup pointers */
  li         x8, 5
  li        x10, 3
  li        x11, 2
  lw        x16, 0(x0)

  /* reset flags for FG0 */
  bn.add    w31, w31, w31

  /* iterate over all limbs for limb-wise subtraction + conditional selection*/
  loop      x30, 5

    /* load a limb of modulus from dmem to w3 */
    bn.lid    x10, 0(x16++)

    /* load the limb of bigint buffer to w2 */
    bn.movr   x11, x8

    /* subtract the current limb of the modulus from current limb of bigint */
    bn.subb   w4, w2, w3

    /* conditionally select subtraction result or unmodified limb */
    bn.sel    w3, w4, w2, FG1.C

    /* move back result from w3 to bigint buffer */
    bn.movr   x8++, x10

  ret


/**
* Compute square of Montgomery modulus
*
* Returns RR = R^2 mod M
*         with M being the Modulus of length 256..4096 bit
*              R = 2^(256*N), N is the number of limbs per bigint
*
* The squared Montgomery modulus (RR) is needed to transform bigints to and
* from the Montgomery domain.
*
* RR is computed in this subroutine by iteratively doubling and reduction.
*
* Flags: The states of both FG0 and FG1 depend on intermediate values and are
*        not usable after return.
*
* @param[in]  w31: all-zero
* @param[in]  x30: N, number of limbs
* @param[out] dmem[dmem[8]]+N*32:dmem[dmem[8]]: computed RR
*
* clobbered registers: x3, x8, x10, x11, x16 to x24
*                      w0, w2, w3, w4, w5 to w20 depending on N
* clobbered flag groups: FG0, FG1
*/
computeRR:
  /* prepare all-zero reg */
  bn.xor    w31, w31, w31

  /* load dmem[0] to w0. This is just used to have a non-zero number
     available */
  li        x3, 0
  bn.lid    x3, 0(x0)

  /* load dmem pointers from dmem[31..0] */
  lw        x16, 0(x0)
  lw        x17, 4(x0)
  lw        x18, 8(x0)
  lw        x19, 12(x0)
  lw        x20, 16(x0)
  lw        x21, 20(x0)
  lw        x22, 24(x0)
  lw        x23, 28(x0)

  /* zeroize w3 */
  bn.xor    w3, w3, w3

  /* compute full length of current bigint size in bits
     N*w = x24 = N*256 = N*2^8 = x22 << 8 */
  slli      x24, x22, 8

  /* reg pointers */
  li        x8, 5
  li        x10, 3

  /* zeroize w3 */
  bn.xor    w3, w3, w3

  /* zeroize all limbs of bigint in regfile */
  loop      x30, 1
    bn.movr   x8++, x10

  /* compute R-M
     since R = 2^(N*w), this can be computed as R-M = unsigned(0-M) */
  bn.sub    w3, w31, w0, FG1
  jal       x1, selcxSub

  /* Compute R^2 mod M = R*2^(N*w) mod M.
     => R^2 mod M can be computed by performing N*w duplications of R.
     We directly perform a modulo reduction in each step such that the
     final result will already be reduced. */
  loop      x24, 16
    /* reset pointer */
    li        x8, 5

    /* zeroize w3 reset flags of FG1 */
    bn.sub    w3, w3, w3, FG1

    /* Duplicate the intermediate bigint result. This can overflow such that
       bit 2^(N*w) (represented by the carry bit after the final loop cycle)
       is set. */
    loop      x30, 3
      /* copy current limb of bigint to w2 */
      bn.movr   x11, x8

      /* perform the doubling */
      bn.addc   w2, w2, w2, FG1

      /* copy result back to bigint in regfile */
      bn.movr   x8++, x11

    /* Conditionally subtract the modulus from the current bigint Y if there
       was an overflow. Again, just considering the lowest N*w bits is
       sufficient, since (in case of an overflow) we can write
       2*Y as 2^(N*w) + X with M > X >= 0.
       Then, 2*Y - M = 2^(N*w) + X - M = X + unsigned(0-M) */
    jal       x1, selcxSub

    /* reset pointer to 1st limb of bigint in regfile */
    li        x8, 5

    /* reset pointer to modulus in dmem */
    lw        x16, 0(x0)

    /* reset flags of FG1 */
    bn.sub    w3, w3, w3, FG1

    /* compare intermediate bigint y with modulus
       subtract modulus if Y > M */
    loop      x30, 3
      bn.lid    x10, 0(x16++)
      bn.movr   x11, x8++
      bn.cmpb   w3, w2, FG1
    jal       x1, selcxSub

    li        x0, 0

  /* reset pointer to 1st limb of bigint in regfile */
  li        x8, 5

  /* store computed RR in dmem */
  loop      x30, 2
    bn.sid    x8, 0(x18++)
    addi      x8, x8, 1

  ret


/**
 * Unrolled 512=256x256 bit multiplication.
 *
 * Returns c = a x b.
 *
 * Flags: No flags are set in this subroutine
 *
 * @param[in] w30: a, first operand
 * @param[in] w25: b, second operand
 * @param[out] [w26, w27]: c, result
 *
 * clobbered registers: w26, w27
 * clobbered flag groups: none
 */
dmXd0:
  bn.mulqacc.z          w30.0, w25.0,  0
  bn.mulqacc            w30.1, w25.0, 64
  bn.mulqacc.so  w27.L, w30.0, w25.1, 64
  bn.mulqacc            w30.2, w25.0,  0
  bn.mulqacc            w30.1, w25.1,  0
  bn.mulqacc            w30.0, w25.2,  0
  bn.mulqacc            w30.3, w25.0, 64
  bn.mulqacc            w30.2, w25.1, 64
  bn.mulqacc            w30.1, w25.2, 64
  bn.mulqacc.so  w27.U, w30.0, w25.3, 64
  bn.mulqacc            w30.3, w25.1,  0
  bn.mulqacc            w30.2, w25.2,  0
  bn.mulqacc            w30.1, w25.3,  0
  bn.mulqacc            w30.3, w25.2, 64
  bn.mulqacc.so  w26.L, w30.2, w25.3, 64
  bn.mulqacc.so  w26.U, w30.3, w25.3,  0

  ret


/**
 * Unrolled 512=256x256 bit multiplication.
 *
 * Returns c = a x b.
 *
 * Flags: No flags are set in this subroutine
 *
 * @param[in] w30: a, first operand
 * @param[in] w2: b, second operand
 * @param[out] [w26, w27]: c, result
 *
 * clobbered registers: w26, w27
 * clobbered flag groups: none
 */
dmXa:
  bn.mulqacc.z          w30.0, w2.0,  0
  bn.mulqacc            w30.1, w2.0, 64
  bn.mulqacc.so  w27.L, w30.0, w2.1, 64
  bn.mulqacc            w30.2, w2.0,  0
  bn.mulqacc            w30.1, w2.1,  0
  bn.mulqacc            w30.0, w2.2,  0
  bn.mulqacc            w30.3, w2.0, 64
  bn.mulqacc            w30.2, w2.1, 64
  bn.mulqacc            w30.1, w2.2, 64
  bn.mulqacc.so  w27.U, w30.0, w2.3, 64
  bn.mulqacc            w30.3, w2.1,  0
  bn.mulqacc            w30.2, w2.2,  0
  bn.mulqacc            w30.1, w2.3,  0
  bn.mulqacc            w30.3, w2.2, 64
  bn.mulqacc.so  w26.L, w30.2, w2.3, 64
  bn.mulqacc.so  w26.U, w30.3, w2.3,  0

  ret


/**
 * Constant time conditional bigint subtraction
 *
 * Returns C <= C-s*B
 *         with B being a bigint of length 256..4096 bit
 *              C being a bigint of length 256..4096 bit
 *              s being a boolean value [0,1]
 *
 * Depending on state of FG1.C subtracts a bigint B located in dmem from
 * another bigint C, located in the wide reg file and stores result at same
 * position in wide reg file.
 *
 * Flags: When leaving this subroutine, flags of FG0 depend on a
 *        potentially discarded value and therefore are not usable after
 *        return. FG1 is not modified in this subroutine.
 *
 * @param[in]  x16: dmem pointer to first limb of subtrahend (B)
 * @param[in]  x8: regfile pointer to first limb of minuend and result (C)
 * @param[in]  FG.C: s, subtraction flag, subtract if 1
 * @param[in]  x30: number of limbs
 * @param[in]  x12: pointer to temp reg, must be set to 30
 * @param[in]  x13: pointer to temp reg, must be set to 24
 * @param[in]  FG0.C: needs to be set to 0
 *
 * clobbered registers: x8, x16, w30, w24, w29, w30, w[x8] to w[x8+N-1], w29
 * clobbered Flag Groups: FG0
 */
mma_sub_cx:

  /* iterate over all limbs for conditional limb-wise subtraction */
  loop      x30, 6
    /* load limb of subtrahend (input B) to w24 */
    bn.lid    x13, 0(x16++)

    /* load limb of minuend (input C) to w30 */
    bn.movr   x12, x8

    /* perform subtraction for a limb */
    bn.subb   w29, w30, w24

    bn.movr   x8, x13

    /* conditionally select subtraction result or unmodified limb */
    bn.sel    w24, w29, w30, FG1.C

    /* store selection result in reg file */
    bn.movr   x8++, x13
  ret


/**
 * Main loop body for constant-time Montgomery Modular Multiplication
 *
 * Returns: C <= (C + A*b_i + M*m0'*(C[0] + A[0]*b_i))/(2^WLEN) mod R
 *
 * This implements the main loop body for the Montgomery Modular Multiplication
 * as well as the conditional subtraction. See e.g. Handbook of Applied
 * Cryptography (HAC) 14.36 (steps 2.1 and 2.2) and step 3.
 * This subroutine has to be called for every iteration of the loop in step 2
 * of HAC 14.36, i.e. once per limb of operand B (x in HAC notation). The limb
 * is supplied via w2. In the explanations below, the index i refers to the
 * i_th call to this subroutine within one full Montgomery Multiplication run.
 * Step 3 of HAC 14.36 is replaced by the approach to perform the conditional
 * subtraction when the intermediate result is larger than R instead of m. See
 * e.g. https://eprint.iacr.org/2017/1057 section 2.4.2 for a justification.
 * This does not omit the conditional subtraction, but simplifies the
 * comparison. The subtraction is carried out in constant time manner.
 * Variable names of HAC are mapped as follows to the ones used in the
 * this library: x=B, y=A, A=C, b=2^WLEN, m=M, R=R, m' = m0', n=N.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  x19: dmem pointer to first limb operand A
 * @param[in]  x31: N-1, number of limbs minus one
 * @param[in]  w2:  current limb of operand B, b_i
 * @param[in]  w3:  Montgomery constant m0'
 * @param[in]  w31: all-zero
 * @param[in]  [w[4+N-1]:w4] intermediate result A
 * @param[out] [w[4+N-1]:w4] intermediate result A
 *
 * clobbered registers: x8, x10, x12, x13, x16, x19
 *                      w24, w25, w26, w27, w28, w29, w30, w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
mma:

  /* pointers to temp. wregs */
  li        x12, 30
  li        x13, 24

  /* buffer read pointer */
  li         x8,  4

  /* buffer write pointer */
  li        x10,  4

  /* load 1st limb of input y (operand a): w30 = y[0] */
  bn.lid    x12, 0(x19++)

  /* This is x_i*y_0 in step 2.1 of HAC 14.36 */
  /* [w26, w27] = w30*w2 = y[0]*x_i */
  jal x1,   dmXa

  /* w24 = w4 = A[0] */
  bn.movr   x13, x8++

  /* add A[0]: [w29, w30] = [w26, w27] + w24 = y[0]*x_i + A[0] */
  bn.add    w30, w27, w24

  /* this serves as c_xy in the first cycle of the loop below */
  bn.addc   w29, w26, w31

  /* w25 = w3 = m0' */
  bn.mov    w25, w3

  /* multiply by m0', this concludes Step 2.1 of HAC 14.36 */
  /* [_, u_i] = [w26, w27] = w30*w25 = (y[0]*x_i + A[0])*m0'*/
  jal       x1, dmXd0


  /* With the computation of u_i, the compuations in a cycle 0 of the loop
     below are already partly done. The following instructions (until the
     start of the loop) implement the remainder, such that cylce 0 can be
     omitted in the loop */

  /* [_, u_i] = [w28, w25] = [w26, w27]  */
  bn.mov    w25, w27
  bn.mov    w28, w26

  /* w24 = w30 =  y[0]*x_i + A[0] mod b */
  bn.mov    w24, w30

  /* load first limb of modulus: w30 = m[0] */
  bn.lid    x12, 0(x16++)

  /* [w26, w27] = w30*w25 = m[0]*u_i*/
  jal x1,   dmXd0

  /* [w28, w27] = [w26, w27] + w24 = m[0]*u_i + (y[0]*x_i + A[0] mod b) */
  bn.add    w27, w27, w24
  /* this serves as c_m in the first cycle of the loop below */
  bn.addc   w28, w26, w31


  /* This loop implements step 2.2 of HAC 14.36 with a word-by-word approach.
     The loop body is subdivided into two steps. Each step performs one
     multiplication and subsequently adds two WLEN sized words to the
     2WLEN-sized result, such that there are no overflows at the end of each
     step-
     Two carry words are required between the cycles. Those are c_xy and c_m.
     Assume that the variable j runs from 1 to N-1 in the explanations below.
     A cycle 0 is omitted, since the results from the computations above are
     re-used */
  loop      x31, 14
    /* Step 1: First multiplication takes a limb of each of the operands and
       computes the product. The carry word from the previous cycle c_xy and
       the j_th limb of the buffer A, A[j] arre added to the multiplication
       result.

    /* load limb of y (operand a) and mult. with x_i: [w26, w27] <= y[j]*x_i */
    bn.lid    x12, 0(x19++)
    jal       x1, dmXa
    /* add limb of buffer: [w26, w27] <= [w26,w27] + w24 = y[j]*x_i + A[j] */
    bn.movr   x13, x8++
    bn.add    w27, w27, w24
    bn.addc   w26, w26, w31
    /* add carry word from previous cycle:
       [c_xy, a_tmp] = [w29, w24] <= [w26,w27] + w29 = y[j]*x_i + A[j] + c_xy*/
    bn.add    w24, w27, w29
    bn.addc   w29, w26, w31


    /* Step 2:  Second multiplication computes the product of a limb m[j] of
       the modulus with u_i. The 2nd carry word from the previous loop cycle
       c_m and the lower word a_tmp of the result of Step 1 are added. */

    /* load limb m[j] of modulus and multiply with u_i:
       [w26, w27] = w30*w25 = m[j+1]*u_i */
    bn.lid    x12, 0(x16++)
    jal       x1, dmXd0
    /* add result from first step
       [w26, w27] <= [w26,w27] + w24 = m[j+1]*u_i + a_tmp */
    bn.add    w27, w27, w24
    bn.addc   w26, w26, w31
    /* [c_m, A[j]] = [w28, w24] = m[j+1]*u_i + a_tmp + c_m */
    bn.add    w24, w27, w28, FG1
    /* store at w[4+j] = A[j-1]
       This includes the reduction by 2^WLEN = 2^b in step 2.2 of HAC 14.36 */
    bn.movr   x10++, x13
    bn.addc   w28, w26, w31, FG1


  /* Most significant limb of A is sum of the carry words of last loop cycle
     A[N-1] = w24 <= w29 + w28 = c_xy + c_m */
  bn.addc   w24, w29, w28, FG1
  bn.movr   x10++, x13

  /* restore clobbered pointers */
  lw        x16, 0(x0)
  lw        x19, 12(x0)
  li        x8, 4
  li        x10, 4
  li        x12, 30
  li        x13, 24

  /* This replaces Step 3 of HAC 14.36 and performs conditional constant-time
     subtraction of the modulus from the output buffer  */
  jal       x1, mma_sub_cx
  nop

  ret


/**
 * Helper functions to setup pointers according to calling conventions
 *
 * Loads dmem pointers from first dmem cell and sets some regfile pointers.
 *
 * Flags: No flags are set in this subroutine
 *
 * @param[in]  dmem[0] dptr_M: dmem pointer to first limb of modulus M
 * @param[in]  dmem[4] dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[in]  dmem[8] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 * @param[in]  dmem[12] dptr_a: dmem pointer to first limb of operand A
 * @param[in]  dmem[16] dptr_b: dmem pointer to first limb of operand B
 * @param[in]  dmem[20] dptr_c: dmem pointer to first limb of result C
 * @param[in]  dmem[24] N: Number of limbs per bignum
 * @param[in]  dmem[28] N-1: Number of limbs per bignum minus 1
 * @param[out]  x16 dptr_M: dmem pointer to first limb of modulus M
 * @param[out]  x17 dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[out]  x18 dptr_RR: dmem pointer to first limb of
 *                           squared Montgomery Modulus RR mod M
 * @param[out]  x19 dptr_a: dmem pointer to first limb of operand A
 * @param[out]  x20 dptr_b: dmem pointer to first limb of operand B
 * @param[out]  x21 dptr_c: dmem pointer to first limb of result C
 * @param[out]  x22 N: number of limbs
 * @param[out]  x23 N-1: number of limbs minus 1
 * @param[out]  x24 dptr_M: dmem pointer to first limb of modulus M
 * @param[out]  x25 dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[out]  x26 dptr_RR: dmem pointer to first limb of
 *                           squared Montgomery Modulus RR mod M
 * @param[out]  x27 dptr_a: dmem pointer to first limb of operand A
 * @param[out]  x28 dptr_b: dmem pointer to first limb of operand B
 * @param[out]  x29 dptr_c: dmem pointer to first limb of result C
 * @param[out]  x30 N: number of limbs
 * @param[out]  x31 N-1: number of limbs minus 1
 * @param[out]  x8: pointer to bignum buffer in regfile
 * @param[out]  x9: pointer to temp reg
 * @param[out]  x10: pointer to bignum buffer in regfile
 * @param[out]  x11: pointer to temp reg
 *
 * clobbered registers: x8 to x11, x16 to x31
 * clobbered Flag Groups: none
 */
setupPtrs:
  lw        x16, 0(x0)
  lw        x17, 4(x0)
  lw        x18, 8(x0)
  lw        x19, 12(x0)
  lw        x20, 16(x0)
  lw        x21, 20(x0)
  lw        x22, 24(x0)
  lw        x23, 28(x0)
  lw        x24, 0(x0)
  lw        x25, 4(x0)
  lw        x26, 8(x0)
  lw        x27, 12(x0)
  lw        x28, 16(x0)
  lw        x29, 20(x0)
  lw        x30, 24(x0)
  lw        x31, 28(x0)
  bn.mov    w1, w31
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  ret


/**
 * Constant-time Montgomery Modular Multiplication
 *
 * Returns: C = montmul(A,B) = A*B*R^(-1) mod M
 *
 * This implements the limb-by-limb interleadved Montgomory Modular
 * Multiplication Algorithm. This is only a wrapper around the main loop body.
 * For algorithmic implementation details see the mma subroutine.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  dmem[0] dptr_M: dmem pointer to first limb of modulus M
 * @param[in]  dmem[4] dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[in]  dmem[8] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 * @param[in]  dmem[12] dptr_a: dmem pointer to first limb of operand A
 * @param[in]  dmem[16] dptr_b: dmem pointer to first limb of operand B
 * @param[in]  dmem[20] dptr_c: dmem pointer to first limb of result C
 * @param[in]  dmem[24] N: Number of limbs per bignum
 * @param[in]  dmem[28] N-1: Number of limbs per bignum minus 1
 * @param[in]  w31: all-zero
 * @param[out] [dmem[dptr_c+N*32-1]:dmem[dptr_c]]: result C
 *
 * clobbered registers: x3, x4, x5, x6, x8 to x13, x16 to x31
 *                      w1 to w3, w24 to w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
mulx:

  /* load pointers from dmem[0] to w0*/
  li        x3, 0
  bn.lid    x3, 0(x0)

  /* prepare pointers and other parameters */
  jal       x1, setupPtrs

  /* load Montgomery constant: w3 = dmem[x17] = dmem[dptr_m0d] = m0'*/
  bn.lid    x9, 0(x17)

  /* init regfile bigint buffer with zeros */
  bn.mov    w2, w31
  loop      x30, 1
    bn.movr   x10++, x11

  /* restore pointer */
  li        x10, 4

  /* iterate over limbs of operand B */
  loop      x30, 8

    /* load limb of operand b */
    bn.lid    x11, 0(x20++)

    /* save some regs */
    add       x4, x16, x0
    add       x5, x19, x0
    add       x6, x20, x0

    /* Main loop body of Montgomory Multiplication algorithm */
    jal       x1, mma

    /* restore regs */
    add       x16, x4, x0
    add       x19, x5, x0
    add       x20, x6, x0

  /* restore pointer */
  li        x8, 4

  /* Store result in dmem starting at dmem[dptr_c] */
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* restore pointer */
  li        x8, 4

  ret


/**
 * Constant time conditional bigint subtraction
 *
 * Returns C = A-x*B
 *         with A being a bigint of length 256..4096 bit
 *              B being a bigint of length 256..4096 bit
 *              C being a bigint of length 256..4096 bit
 *              x being a boolean value [0,1]
 *
 * Depending on state of FG1.C subtracts a bigint B located in dmem from
 * another bigint A, located in the wide reg file and stores result C in dmem.
 *
 * Flags: When leaving this subroutine, flags of FG0 depend on a
 *        potentially discarded value and therefore are not usable after
 *        return. FG1 is not modified in this subroutine.
 *
 * @param[in]  x16: dmem pointer to first limb of subtrahend (B)
 * @param[in]  x8: regfile pointer to first limb of minuend (input A)
 * @param[in]  x21: dmem pointer to first limb of result (C)
 * @param[in]  x30: N, number of limbs
 * @param[in]  FG1.C: subtraction condition, subtract if 1 (x)
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[in]  FG0.C: needs to be set to 0
 *
 * clobbered registers: x8, x16, x21, w2, w3
 * clobbered Flag Groups: FG0
 */
mm1_sub_cx:
  /* iterate over all limbs for conditional limb-wise subtraction */
  loop      x30, 5
    /* load limb of subtrahend (input B): w3 = dmem[x16+i] */
    bn.lid    x9, 0(x16++)

    /* move limb from bignum bufer to w2 */
    bn.movr   x11, x8++

    /* perform subtraction for a limb w3 = w2-1 */
    bn.subb   w3, w2, w3

    /* conditionally select subtraction result or unmodified limb */
    bn.sel    w2, w3, w2, FG1.C

    /* store selection result in dmem */
    bn.sid    x11, 0(x21++)

  ret


/**
 * Constant-time Montgomery modular multiply by one
 *
 * Returns: C = montmul(1,A) = A*R^(-1) mod M
 *
 * Routine for back-conversion from Montgomery domain.
 * This implements the limb-by-limb interleadved Montgomory Modular
 * Multiplication Algorithm, with one operand fixed to 1. This is only a
 * wrapper around the main loop body. For algorithmic implementation details
 * see the mma subroutine.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  x19: dmem pointer to first limb of operand A
 * @param[in]  x21: dmem pointer to first limb of result C
 * @param[in]  x30: N, number of limbs
 * @param[in]  x31: N-1, number of limbs minus one
 * @param[in]  x8: pointer to temp reg, must be set to 4
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[in]  w3: Montgomery constant m0'
 * @param[in]  w31: all-zero
 *
 * clobbered registers: x6, x7, x8, x9, x10, x12, x13, x16, x19, x21
 *                      w2. w3. w24, w25, w26, w27, w28, w29, w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
mul1_exp:
  /* load Montgomery constant: w3 = dmem[x17] = dmem[dptr_m0d] = m0' */
  bn.lid    x9, 0(x17)

  /* init regfile bigint buffer with zeros */
  bn.mov    w2, w31
  loop      x30, 1
    bn.movr   x10++, x11

  /* w2=1 this is operand B */
  bn.xor    w2, w2, w2
  bn.addi   w2, w2, 1

  /* save dmem pointers for operand A and modulus */
  addi      x6, x16, 0
  addi      x7, x19, 0

  /* iterate over limbs of operand B */
  loop      x30, 4

    /* restore  dmem pointers for operand A and modulus */
    addi      x16, x6, 0
    addi      x19, x7, 0

    /* Main loop body of Montgomory Multiplication algorithm */
    /* 1[i]*A */
    jal       x1, mma

    /* all subsequent limbs of operand B are zero since B=1 */
    bn.mov    w2, w31

  /* restore dmem pointers for operand A and modulus */
  addi      x16, x6, 0
  addi      x19, x7, 0

  /* zeroize w2 and clear flags */
  bn.sub    w2, w2, w2, FG1

  /* iterate over all limbs of bigint buffer for limbwise comparison of
     buffer with the Modulus. After last loop cycle, FG1.C is set if bigint
     in buffer is larger than Modulus */
  loop      x30, 3

    /* load limb of limb of Modulus to w3 */
    bn.lid    x9, 0(x16++)

    /* load limb from bigint buffer to w2 */
    bn.movr   x11, x8++

    /* compare limb of flag with limb of Modulus */
    bn.cmpb   w3, w2, FG1

  /* restore pointers to bigint buffer in regfile */
  li         x8, 4
  li        x10, 4

  /* restore  dmem pointers for operand A and modulus */
  addi      x16, x6, 0
  addi      x19, x7, 0

  /* conditionally subtract Modulus from buffer and store result in
     dmem[x21] to dmem[x21+N] */
  jal       x1, mm1_sub_cx

  /* restore  dmem pointers for operand A and modulus */
  addi      x16, x6, 0
  addi      x19, x7, 0

  ret


/**
 * Externally callable wrapper for Montgomery modular multiply by one
 *
 * Returns: C = montmul(1,A) = A*R^(-1) mod M
 *
 * Routine for back-conversion from Montgomery domain.
 * This implements the limb-by-limb interleadved Montgomory Modular
 * Multiplication Algorithm, with one operand fixed to 1. This is only a
 * wrapper around the main loop body. For algorithmic implementation details
 * see the mma subroutine.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  dmem[0] dptr_M: dmem pointer to first limb of modulus M
 * @param[in]  dmem[4] dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[in]  dmem[8] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 * @param[in]  dmem[12] dptr_a: dmem pointer to first limb of operand A
 * @param[in]  dmem[20] dptr_c: dmem pointer to first limb of result C
 * @param[in]  dmem[24] N: Number of limbs per bignum
 * @param[in]  dmem[28] N-1: Number of limbs per bignum minus 1
 * @param[in]  w31: all-zero
 * @param[out] [dmem[dptr_c+N*32-1]:dmem[dptr_c]]: result C
 *
 * clobbered registers: x3, x4, x5, x6 to x13, x16 to x31
 *                      w1 to w3, w24 to w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
mul1:
  /* load pointers from dmem[0] to w0*/
  li        x3, 0
  bn.lid    x3, 0(x0)

  /* prepare pointers and other parameters */
  jal       x1, setupPtrs

  /* call montmul(1,A) algorithm */
  jal       x1, mul1_exp

  ecall


/**
 * Constant-time Montgomery Modular Multiplication
 *
 * Returns: C = montmul(A,B) = A*B*R^(-1) mod M
 *
 * This implements the limb-by-limb interleadved Montgomory Modular
 * Multiplication Algorithm. This is only a wrapper around the main loop body.
 * For algorithmic implementation details see the mma subroutine.
 *
 * This variant loads the 3rd descriptor (dmem cell 2) and stores the result
 * in dmem. It is intended to be used as squaring primitive in a
 * square and multiply implementation.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  dmem[32] dptr_M: dmem pointer to first limb of modulus M
 * @param[in]  dmem[36] dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[in]  dmem[40] dptr_RR: dmem pointer to first limb of
 *                               squared Montgomery Modulus RR mod M
 * @param[in]  dmem[44] dptr_a: dmem pointer to first limb of operand A
 * @param[in]  dmem[48] dptr_b: dmem pointer to first limb of operand B
 * @param[in]  dmem[52] dptr_c: dmem pointer to first limb of result C
 * @param[in]  dmem[56] N: Number of limbs per bignum
 * @param[in]  dmem[60] N-1: Number of limbs per bignum minus 1
 * @param[in]  w31: all-zero
 * @param[in]  x30: N, number of limbs
 * @param[in]  x31: N-1, number of limbs minus one
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 *
 * clobbered registers: x5, x6, x7, x8, x10, x12, x13, x16 to x23
 *                      w2, w3, w24 to w30, w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
sqrx_exp:
  /* load pointers from 2nd dmem descriptor (cell 1) */
  lw        x16, 32(x0)
  lw        x17, 36(x0)
  lw        x18, 40(x0)
  lw        x19, 44(x0)
  lw        x20, 48(x0)
  lw        x21, 52(x0)
  lw        x22, 56(x0)
  lw        x23, 60(x0)

  /* load Montgomery constant: w3 = dmem[x17] = dmem[dptr_m0d] = m0' */
  bn.lid    x9, 0(x17)

    /* init regfile bigint buffer with zeros */
  bn.mov    w2, w31
  loop      x30, 1
    bn.movr   x10++, x11

  /* set pointer */
  lw        x10, 8(x0)

  /* iterate over limbs of operand B */
  loop      x30, 8

    /* load limb of operand b */
    bn.lid    x11, 0(x20++)

    /* save some regs */
    addi      x5, x20, 0
    addi      x6, x16, 0
    addi      x7, x19, 0

    /* Main loop body of Montgomory Multiplication algorithm */
    jal       x1, mma

    /* restore regs */
    addi      x20, x5, 0
    addi      x16, x6, 0
    addi      x19, x7, 0

  /* restore pointers */
  li        x10, 4
  li         x8, 4

  /* Store result in dmem starting at dmem[dptr_c] */
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* restore pointers */
  li         x8, 4
  li        x10, 4
  lw        x12, 16(x0)
  lw        x13, 20(x0)

  ret


/**
 * Constant-time Montgomery Modular Multiplication
 *
 * Returns: C = montmul(A,B) = A*B*R^(-1) mod M
 *
 * This implements the limb-by-limb interleadved Montgomory Modular
 * Multiplication Algorithm. This is only a wrapper around the main loop body.
 * For algorithmic implementation details see the mma subroutine.
 *
 * This variant loads the 2nd descriptor (dmem cell 1) and stores the result
 * in the regfile. It is intended to be used as multiplication primitive in a
 * square and multiply implementation.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  dmem[64] dptr_M: dmem pointer to first limb of modulus M
 * @param[in]  dmem[68] dptr_m0d: dmem pointer to Montgomery Constant m0'
 * @param[in]  dmem[71] dptr_RR: dmem pointer to first limb of
 *                               squared Montgomery Modulus RR mod M
 * @param[in]  dmem[76] dptr_a: dmem pointer to first limb of operand A
 * @param[in]  dmem[80] dptr_b: dmem pointer to first limb of operand B
 * @param[in]  dmem[88] N: Number of limbs per bignum
 * @param[in]  dmem[92] N-1: Number of limbs per bignum minus 1
 * @param[in]  w31: all-zero
 * @param[in]  x30: N, number of limbs
 * @param[in]  x31: N-1, number of limbs minus one
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[out] [w[4+N-1]:w4]: result C
 *
 * clobbered registers: x5, x6, x7, x8, x10, x12, x13, x16 to x23
 *                      w2, w3, w24 to w30, w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
mulx_exp:
  /* load pointers from 3rd dmem descriptor (cell 2) */
  lw        x16, 64(x0)
  lw        x17, 68(x0)
  lw        x18, 72(x0)
  lw        x19, 76(x0)
  lw        x20, 80(x0)
  lw        x21, 84(x0)
  lw        x22, 88(x0)
  lw        x23, 92(x0)

  /* load Montgomery constant: w3 = dmem[x17] = dmem[dptr_m0d] = m0' */
  bn.lid    x9, 0(x17)

  /* init regfile bigint buffer with zeros */
  bn.mov    w2, w31
  loop      x30, 1
    bn.movr   x10++, x11

  /* set pointers */
  li         x8, 4
  li        x10, 4
  lw        x12, 16(x0)
  lw        x13, 20(x0)

  /* iterate over limbs of operand B */
  loop      x30, 8

    /* load limb of operand b */
    bn.lid    x11, 0(x20++)

    /* save some regs */
    addi      x5, x20, 0
    addi      x6, x16, 0
    addi      x7, x19, 0

    /* Main loop body of Montgomory Multiplication algorithm */
    jal       x1, mma

    /* restore regs */
    addi      x20, x5, 0
    addi      x16, x6, 0
    addi      x19, x7, 0

  /* restore pointers */
  li        x8, 4
  li        x10, 4
  lw        x12, 16(x0)
  lw        x13, 20(x0)

  ret


/**
 * Conditionally overwrite bigint in dmem
 *
 * Depending on state of FG0.C overwrites a bigint in dmem with one from
 * a buffer in the wide reg file.
 *
 * Flags: Does not set any flags, does not use flags except FG0.C
 *
 * @param[in]  x21: dptr, pointer to first limb of bigint in dmem
 * @param[in]  x8: rptr, pointer to first limb of bigint in regfile buffer
 * @param[in]  FG.C: selection condition, overwrite dmem when FG0.C==1
 * @param[in]  x30: number of limbs
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x11: pointer to temp reg, must be set to 2
 *
 * clobbered registers: x8, x21, w0, w2
 * clobbered Flag Groups: none
 */
selOutOrC:
  /* iterate over all limbs */
  loop      x30, 6

    /* load limb from dmem */
    bn.lid    x9, 0(x21)

    /* store limb to dmem */
    bn.sid    x11, 0(x21)

    /* load limb from regfile buffer */
    bn.movr   x11, x8++
    bn.mov    w0, w2

    /* conditional select: w2 = FG0.C?w[x8+i]:dmem[x21+i] */
    bn.sel    w2, w0, w3, C

    /* store selected limb to dmem */
    bn.sid    x11, 0(x21++)

  ret


/**
 * Constant-time bigint modular exponentiation
 *
 * Returns: C = modexp(A,E) = A^E mod M
 *
 * This implements the square and multiply algorithm, i.e. for each bit of the
 * exponent both the squared only and the squared with multiply results are
 * computed but one result is discarded.
 * Computation is carried out in the Montgomery domain, by using the primitives
 * mulx, sqrx_exp, mulx_exp and mul1_exp.
 * The squared Montgomery modulus RR and the Montgomery constant m0' have to
 * be precomputed and provided at the appropriate locations in dmem.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * Calling convention:
 * Data is loaded and stored to and from dmem in accordance to four
 *   descriptors that have to be provided in the first 4 dmem cells
 *   (256 bit each).
 *
 * first descriptor used to convert to montgomery domain:
 *   @param[in]  dmem[0] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[4] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[8] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[12] dptr_a_mont: dmem pointer to first limb of base A
 *   @param[in]  dmem[16] dptr_b_mont: dmem pointer to first limb of RR
 *   @param[in]  dmem[20] dptr_c_mont: dmem pointer to first limb of base A
 *   @param[in]  dmem[24] N: Number of limbs per bignum
 *   @param[in]  dmem[28] N-1: Number of limbs per bignum minus 1
 *
 * second descriptor used for squaring:
 *   @param[in]  dmem[32] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[36] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[40] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[44] dptr_a_sqr: dmem pointer to first limb of result C
 *   @param[in]  dmem[48] dptr_b_sqr: dmem pointer to first limb of result C
 *   @param[in]  dmem[52] dptr_c_sqr: dmem pointer to first limb of result C
 *   @param[in]  dmem[56] N: Number of limbs per bignum
 *   @param[in]  dmem[60] N-1: Number of limbs per bignum minus 1
 *
 * third descriptor used for multiplication:
 *   @param[in]  dmem[64] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[68] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[72] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[76] dptr_a_mul: dmem pointer to first limb of base A
 *   @param[in]  dmem[80] dptr_b_mul: dmem pointer to first limb of result C
 *   @param[in]  dmem[84] dptr_c_mul: dmem pointer to first limb of result C
 *   @param[in]  dmem[88] N: Number of limbs per bignum
 *   @param[in]  dmem[92] N-1: Number of limbs per bignum minus 1
 *
 * fourth descriptor used for reading the exponent and back-conversion:
 *   @param[in]  dmem[96] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[100] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[104] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[108] dptr_a_ex1: dmem pointer to first limb of base A
 *   @param[in]  dmem[112] dptr_b_ex1: dmem pointer to first limb of exponent E
 *   @param[in]  dmem[116] dptr_c_ex1: dmem pointer to first limb of result C
 *   @param[in]  dmem[120] N: Number of limbs per bignum
 *   @param[in]  dmem[124] N-1: Number of limbs per bignum minus 1
 *
 * clobbered registers: x3 to x13, x16 to x31
 *                      w0 to w3, w24 to w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
modexp:
  /* convert to montgomery domain montmul(A,RR) */
  jal       x1, mulx

  /* load pointers from 4th descriptor (cell 3) */
  lw        x16, 96(x0)
  lw        x17, 100(x0)
  lw        x18, 104(x0)
  lw        x19, 108(x0)
  lw        x20, 112(x0)
  lw        x21, 116(x0)
  lw        x22, 120(x0)
  lw        x23, 124(x0)

  /* zeroize w2 and reset flags */
  bn.sub    w2, w2, w2

  /* this loop initializes the output buffer with -M */
  loop      x30, 3
    /* load limb from modulus */
    bn.lid    x11, 0(x16++)

    /* subtract limb from 0 */
    bn.subb   w2, w31, w2

    /* store limb in dmem */
    bn.sid    x11, 0(x21++)

  /* compute bit length of current bigint size */
  slli      x24, x22, 8

  /* iterate over all bits of bigint */
  loop      x24, 17
    /* square */
    jal       x1, sqrx_exp

    /* multiply */
    jal       x1, mulx_exp

    /* reload pointers */
    lw        x16, 96(x0)
    lw        x17, 100(x0)
    lw        x18, 104(x0)
    lw        x19, 108(x0)
    lw        x20, 112(x0)
    lw        x21, 116(x0)
    lw        x22, 120(x0)
    lw        x23, 124(x0)

    /* w2 <= w2 << 1 */
    bn.add    w2, w2, w2

    /* the loop performs a 1-bit left shift of the exponent. Last MSB moves
       to FG0.C, such that it can be used for selection */
    loop      x30, 3
      bn.lid    x11, 0(x20)
      /* w2 <= w2 << 1 */
      bn.addc   w2, w2, w2
      bn.sid    x11, 0(x20++)

    /* select squared or squared+multiplied result */
    jal       x1, selOutOrC

    nop

  /* load 4th descriptor to w0 */
  li        x3, 0
  bn.lid    x3, 96(x0)

  /* restore pointers */
  lw        x16, 96(x0)
  lw        x17, 100(x0)
  lw        x18, 104(x0)
  lw        x19, 108(x0)
  lw        x20, 112(x0)
  lw        x21, 116(x0)
  lw        x22, 120(x0)
  lw        x23, 124(x0)

  /* convert back from montgomery domain */
  jal       x1, mul1_exp

  ecall


/**
 * Bigint modular exponentiation with fixed exponent of 65537
 *
 * Returns: C = modexp(A,65537) = A^65537 mod M
 *
 * This implements the square and multiply algorithm for the fixed exponent
 * of E=65537. Note that this implementation (in contrast to modexp) runs the
 * multiplication step only for bits being actually set in the exponent.
 * Since the exponent is fixed, this is inherently constant-time.
 *
 * The squared Montgomery modulus RR and the Montgomery constant m0' have to
 * be precomputed and provided at the appropriate locations in dmem.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * Calling convention:
 * Data is loaded and stored to and from dmem in accordance to four
 *   descriptors that have to be provided in the first 4 dmem cells
 *   (256 bit each).
 *
 * first descriptor used to convert to montgomery domain:
 *   @param[in]  dmem[0] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[4] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[8] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[12] dptr_a_mont: dmem pointer to first limb of base A
 *   @param[in]  dmem[16] dptr_b_mont: dmem pointer to first limb of RR
 *   @param[in]  dmem[20] dptr_c_mont: dmem pointer to first limb of base A
 *   @param[in]  dmem[24] N: Number of limbs per bignum
 *   @param[in]  dmem[28] N-1: Number of limbs per bignum minus 1
 *
 * second descriptor used for squaring:
 *   @param[in]  dmem[32] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[36] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[40] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[44] dptr_a_sqr: dmem pointer to first limb of result C
 *   @param[in]  dmem[48] dptr_b_sqr: dmem pointer to first limb of result C
 *   @param[in]  dmem[52] dptr_c_sqr: dmem pointer to first limb of result C
 *   @param[in]  dmem[56] N: Number of limbs per bignum
 *   @param[in]  dmem[60] N-1: Number of limbs per bignum minus 1
 *
 * third descriptor used for multiplication:
 *   @param[in]  dmem[64] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[68] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[72] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[76] dptr_a_mul: dmem pointer to first limb of base A
 *   @param[in]  dmem[80] dptr_b_mul: dmem pointer to first limb of result C
 *   @param[in]  dmem[84] dptr_c_mul: dmem pointer to first limb of result C
 *   @param[in]  dmem[88] N: Number of limbs per bignum
 *   @param[in]  dmem[92] N-1: Number of limbs per bignum minus 1
 *
 * fourth descriptor used for back-conversion:
 *   @param[in]  dmem[96] dptr_M: dmem pointer to first limb of modulus M
 *   @param[in]  dmem[100] dptr_m0d: dmem pointer to Montgomery Constant m0'
 *   @param[in]  dmem[104] dptr_RR: dmem pointer to first limb of
 *                              squared Montgomery Modulus RR mod M
 *   @param[in]  dmem[108] dptr_a_ex1: dmem pointer to first limb of base A
 *   @param[in]  dmem[116] dptr_c_ex1: dmem pointer to first limb of result C
 *   @param[in]  dmem[120] N: Number of limbs per bignum
 *   @param[in]  dmem[124] N-1: Number of limbs per bignum minus 1
 *
 * clobbered registers: x3 to x13, x16 to x31
 *                      w0 to w3, w24 to w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
modexp_65537:
  /* convert to montgomery domain montmul(A,RR)
  in = montmul(A,RR) = C*R mod M */
  jal       x1, mulx

  /* pointer to out buffer */
  lw        x21, 116(x0)

  /* zeroize w2 and reset flags */
  bn.sub    w2, w2, w2

  /* this loop initializes the output buffer with -M */
  loop      x30, 3
    /* load limb from modulus */
    bn.lid    x11, 0(x16++)

    /* subtract limb from 0 */
    bn.subb   w2, w31, w2

    /* store limb in dmem */
    bn.sid    x11, 0(x21++)

  /* 65537 = 0b10000000000000001
               ^ sqr + mult
    out = montmul(out,out)       */
  jal       x1, sqrx_exp

  /* out = montmul(in,out)       */
  jal       x1, mulx_exp

  /* store multiplication result in output buffer */
  li        x8, 4
  loop      x30, 2
    /* store selected limb to dmem */
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* 65537 = 0b10000000000000001
                ^<< 16 x sqr >>^   */
  loopi      16, 2
    /* square: out = montmul(out, out) */
    jal       x1, sqrx_exp
    nop

  /* 65537 = 0b10000000000000001
                          mult ^
     out = montmul(in,out)       */
  jal       x1, mulx_exp

  /* store multiplication result in output buffer */
  li        x8, 4
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* pointer to out buffer */
  lw        x19, 108(x0)
  /* pointer to out buffer */
  lw        x21, 116(x0)

  /* convert back from montgomery domain */
  /* out = montmul(out,1) = out/R mod M  */
  jal       x1, mul1_exp

  ecall


/**
 * Externally callable wrapper for computing Montgomery parameters
 *
 * Computes:
 *   - Montgomery Constant m0'
 *   - Squared Montgomery modulus RR mod N
 *
 * Needs to be executed once per constant Modulus.
 *
 * @param[in]  dmem[0] dptr_M: pointer to first limb of modulus in dmem
 * @param[in]  dmem[1] dptr_m0d: pointer to m0' in dmem
 * @param[in]  dmem[2] dptr_RR: pointer to RR in dmem
 * @param[in]  dmem[6] N: Number of limbs per bignum
 * @param[out] [dmem[dptr_m0d+31]:dmem[dptr_m0d]] computed m0'
 * @parma[out] [dmem[dptr_RR+N*32-1]:dmem[dptr_RR]] computed RR
 */
modload:

  /* prepare all-zero reg */
  bn.xor   w31, w31, w31

  /* setup pointers */
  li       x3, 0
  bn.lid   x3, 0(x0)
  lw       x16, 0(x0)
  lw       x17, 4(x0)
  lw       x18, 8(x0)
  lw       x19, 12(x0)
  lw       x20, 16(x0)
  lw       x21, 20(x0)
  lw       x22, 24(x0)
  lw       x23, 28(x0)
  lw       x24, 0(x0)
  lw       x25, 4(x0)
  lw       x26, 8(x0)
  lw       x27, 12(x0)
  lw       x28, 16(x0)
  lw       x29, 20(x0)
  lw       x30, 24(x0)
  lw       x31, 28(x0)
  li       x8, 28
  li       x9, 29
  lw       x10, 8(x0)
  lw       x11, 12(x0)
  lw       x12, 16(x0)
  lw       x13, 20(x0)
  lw       x14, 24(x0)
  lw       x15, 28(x0)
  bn.lid   x8, 0(x16)

  /* Compute Montgomery constant */
  jal      x1, d0inv

  /* Store Montgomery constant in dmem */
  bn.sid   x9, 0(x17)

  /* Compute square of Montgomery modulus */
  jal      x1, computeRR

  ecall
