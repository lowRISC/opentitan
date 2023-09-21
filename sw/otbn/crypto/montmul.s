/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c
 */


.text
.globl modload
.globl montmul
.globl mont_loop

/**
 * Precomputation of a constant m0' for Montgomery modular arithmetic
 *
 * Word-wise Montgomery modular arithmetic requires a quantity m0' to be
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
m0inv:
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
 * value is selected when FG1.C equals 1, otherwise the unmodified value is
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
 * @param[in]  x16: dptr_m, pointer to 1st limb of modulus M
 * @param[in]  x30: N, number of 256 bit limbs in modulus and bigint
 * @param[in]  w31: all-zero
 * @param[in]  FG1.C: s, selection flag
 * @param[out] [w[5+N-1]:w5]: new bigint value
 * @param[in]  FG0.C: needs to be set to 0
 *
 * clobbered registers: x8, x10, x11, x16, w2, w3, w4, w5 to w[5+N-1]
 * clobbered flag groups: FG0
 */
cond_sub_mod:

  /* setup pointers */
  li         x8, 5
  li        x10, 3
  li        x11, 2

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
* @param[in]  x16: dptr_M, pointer to first limb of modulus in dmem
* @param[in]  x18: dptr_RR: dmem pointer to first limb of output buffer for RR
* @param[in]  x30: N, number of limbs
* @param[in]  w31: all-zero
* @param[out] dmem[dptr_RR+N*32:dptr_RR]: computed RR
*
* clobbered registers: x3, x8, x10, x11, x22
*                      w0, w2, w3, w4, w5 to w20 depending on N
* clobbered flag groups: FG0, FG1
*/
compute_rr:
  /* save pointer to modulus */
  addi      x22, x16, 0

  /* zeroize w3 */
  bn.xor    w3, w3, w3

  /* compute full length of current bigint size in bits
     N*w = x24 = N*256 = N*2^8 = x30 << 8 */
  slli      x24, x30, 8

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
  bn.addi w0, w31, 1
  bn.sub    w3, w31, w0, FG1
  addi      x16, x22, 0
  jal       x1, cond_sub_mod

  /* Compute R^2 mod M = R*2^(N*w) mod M.
     => R^2 mod M can be computed by performing N*w duplications of R.
     We directly perform a modulo reduction in each step such that the
     final result will already be reduced. */
  loop      x24, 18
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
    addi      x16, x22, 0
    jal       x1, cond_sub_mod

    /* reset pointer to 1st limb of bigint in regfile */
    li        x8, 5

    /* reset pointer to modulus in dmem */
    addi      x16, x22, 0

    /* reset flags of FG1 */
    bn.sub    w3, w3, w3, FG1

    /* compare intermediate bigint y with modulus
       subtract modulus if Y > M */
    loop      x30, 3
      bn.lid    x10, 0(x16++)
      bn.movr   x11, x8++
      bn.cmpb   w3, w2, FG1
    addi      x16, x22, 0
    jal       x1, cond_sub_mod

    li        x0, 0

  /* reset pointer to 1st limb of bigint in regfile */
  li        x8, 5

  /* reset pointer to modulus */
  addi      x16, x22, 0

  /* store computed RR in dmem */
  addi      x3, x18, 0
  loop      x30, 2
    bn.sid    x8, 0(x3++)
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
mul256_w30xw25:
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
mul256_w30xw2:
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
 * @param[in]  FG0.C: needs to be set to 0
 *
 * clobbered registers: x8, x16, w24, w29, w30, w[x8] to w[x8+N-1]
 * clobbered Flag Groups: FG0
 */
cond_sub_to_reg:

  /* load pointers to temp regs */
  li        x12, 30
  li        x13, 24

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
 * clobbered registers: x8, x10, x12, x13, x16, x19, x22
 *                      w24, w25, w26, w27, w28, w29, w30, w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
mont_loop:
  /* save pointer to modulus */
  addi      x22, x16, 0

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
  jal x1,   mul256_w30xw2

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
  jal       x1, mul256_w30xw25


  /* With the computation of u_i, the computations in a cycle 0 of the loop
     below are already partly done. The following instructions (until the
     start of the loop) implement the remainder, such that cycle 0 can be
     omitted in the loop */

  /* [_, u_i] = [w28, w25] = [w26, w27]  */
  bn.mov    w25, w27
  bn.mov    w28, w26

  /* w24 = w30 =  y[0]*x_i + A[0] mod b */
  bn.mov    w24, w30

  /* load first limb of modulus: w30 = m[0] */
  bn.lid    x12, 0(x16++)

  /* [w26, w27] = w30*w25 = m[0]*u_i*/
  jal x1,   mul256_w30xw25

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
       the j_th limb of the buffer A, A[j] are added to the multiplication
       result.

    /* load limb of y (operand a) and mult. with x_i: [w26, w27] <= y[j]*x_i */
    bn.lid    x12, 0(x19++)
    jal       x1, mul256_w30xw2
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
    jal       x1, mul256_w30xw25
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

  /* restore pointers */
  addi      x16, x22, 0
  li        x8, 4
  li        x10, 4

  /* This replaces Step 3 of HAC 14.36 and performs conditional constant-time
     subtraction of the modulus from the output buffer. */
  jal       x1, cond_sub_to_reg

  /* restore pointer again */
  addi      x16, x22, 0

  /* restore pointer */
  li        x8, 4

  ret


/**
 * Constant-time Montgomery Modular Multiplication
 *
 * Returns: C = montmul(A,B) = A*B*R^(-1) mod M
 *
 * This implements the limb-by-limb interleaved Montgomery Modular
 * Multiplication Algorithm. This is only a wrapper around the main loop body.
 * For algorithmic implementation details see the mont_loop subroutine.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  x16: dptr_M, dmem pointer to first limb of modulus M
 * @param[in]  x17: dptr_m0d, dmem pointer to Montgomery Constant m0'
 * @param[in]  x19: dptr_a, dmem pointer to first limb of operand A
 * @param[in]  x20: dptr_b, dmem pointer to first limb of operand B
 * @param[in]  w31: all-zero
 * @param[in]  x30: N, number of limbs
 * @param[in]  x31: N-1, number of limbs minus one
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[out] [w[4+N-1]:w4]: result C
 *
 * clobbered registers: x5, x6, x7, x8, x10, x12, x13, x20, x22
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * clobbered Flag Groups: FG0, FG1
 */
montmul:
  /* load Montgomery constant: w3 = dmem[x17] = dmem[dptr_m0d] = m0' */
  bn.lid    x9, 0(x17)

  /* init regfile bigint buffer with zeros */
  bn.mov    w2, w31
  loop      x30, 1
    bn.movr   x10++, x11

  /* iterate over limbs of operand B */
  loop      x30, 8

    /* load limb of operand b */
    bn.lid    x11, 0(x20++)

    /* save some regs */
    addi      x5, x20, 0
    addi      x6, x16, 0
    addi      x7, x19, 0

    /* Main loop body of Montgomery Multiplication algorithm */
    jal       x1, mont_loop

    /* restore regs */
    addi      x20, x5, 0
    addi      x16, x6, 0
    addi      x19, x7, 0

  /* restore pointers */
  li        x8, 4
  li        x10, 4

  ret


/**
 * Externally callable wrapper for computing Montgomery parameters
 *
 * Computes:
 *   - Montgomery Constant m0'
 *   - Squared Montgomery modulus RR mod N
 *
 * Needs to be executed once per constant Modulus.
 *
 * @param[in]  x16: dptr_M, dmem pointer to first limb of modulus M
 * @param[in]  x17: dptr_m0d, dmem pointer to buffer for m0'
 * @param[in]  x18: dptr_RR, dmem pointer to buffer for RR
 * @param[in]  x30: N, number of limbs per bignum
 * @param[in]  w31: all-zero
 * @param[out] [dmem[dptr_m0d+31]:dmem[dptr_m0d]] computed m0'
 * @param[out] [dmem[dptr_RR+N*32-1]:dmem[dptr_RR]] computed RR
 */
modload:
  /* load lowest limb of modulus to w28 */
  li       x8, 28
  bn.lid   x8, 0(x16)

  /* Compute Montgomery constant */
  jal      x1, m0inv

  /* Store Montgomery constant in dmem */
  li       x9, 29
  bn.sid   x9, 0(x17)

  /* Compute square of Montgomery modulus */
  jal      x1, compute_rr

  ret
