/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c
 */


.text
.globl modexp_var

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
 * @param[in]  x16: dptr_m, pointer to modulus M in dmem
 * @param[in]  x17: dptr_m0inv, pointer to dmem location to store m0inv
 * @param[in]  w31: all-zero.
 *
 * clobbered registers: x8, w0, w1, w28, w29
 * clobbered flag groups: FG0
 */
compute_m0inv:

  /* load lowest limb of modulus to w28 */
  li       x8, 28
  bn.lid   x8, 0(x16)

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

    /* Store Montgomery constant in dmem */
  li       x8, 29
  bn.sid   x8, 0(x17)

  ret


/**
 * Variable time multi-limb bigint compare
 *
 * Compares two bigints (a, b) located in regfile (a) and dmem (b).
 *
 * Flags: When leaving this subroutine, flags of FG1 depend on the comparison
 *        result of the highest unequal limba, or, if all limbs are equal on
 *        those of the lowest limbs.
 *
 * @param[in] x10: constant 3, used as pointer to w3
 * @param[in] x11: constant 2, used as pointer to w2
 * @param[in] x8: rptr_a, pointer to lowest limb of a in regfile
 * @param[in] x9: rptr_a_h, pointer to highest limb of a in regfile
 * @param[in] x17: dptr_b_h, pointer to highest limb of b in dmem
 * @param[out] x3, bit 0: (b > a), equals FG1.C
 * @param[out] x3, bit 3: (a == b), equals FG1.Z
 *
 * clobbered registers: x3, x5, x7, x9, x17, x19, w2, w3
 * clobbered flag groups: FG1
 */
cmp_dmem_reg_buf:

  addi      x19, x17, 0
  addi      x7, x9, 0

  cmp_loop:

  /* load limbs from dmem and regfile: w2 <= a[i]; w3 <= b[i] */
  bn.lid    x10, 0(x19)
  bn.movr   x11, x7

  /* compare limbs and store comparison result in x3 */
  bn.cmp    w2, w3, FG1
  csrrs     x3, FG1, x0

  /* leave loop if lowest limb was reached */
  beq       x8, x7, cmp_end

  /* reduce limb pointers */
  addi      x19, x19, -32
  addi      x7, x7, -1

  /* if limbs were equal (FG1.Z == 1), compare next lower limb */
  andi      x5, x3, 8
  bne       x5, x0, cmp_loop

  cmp_end:
  nop
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
* @param[in]  x16: dptr_n, pointer to first limb of modulus in dmem
* @param[in]  x18: dptr_rr: dmem pointer to first limb of output buffer for RR
* @param[in]  x30: N, number of limbs
* @param[in]  x31: N-1, number of limbs minus 1
* @param[in]  w31: all-zero
* @param[out] dmem[x18+N*32:x18]: computed RR
*
* clobbered registers: x3, x4, x5, x8, x9, x10, x11, x16, x18, x22, x24
*                      w0, w2, w3, w4, w5 to w20 depending on N
* clobbered flag groups: FG0, FG1
*/
compute_rr:
  /* save pointer to modulus x22 <= dptr_m = x16 */
  addi      x22, x16, 0

  /* x17 = dptr_m + (N-1)*32 points to highest limb of modulus in dmem */
  slli      x17, x31, 5
  add       x17, x22, x17

  li        x8, 5

  /* x9 = rptr_buf_h <= rptr_buf + N-1 */
  add       x9, x31, x8

  /* compute full length of current bigint size in bits
     N*w = x24 <= N*256 = N*2^8 = x30 << 8 */
  slli      x24, x30, 8

  /* reg pointers to current limb of buffer and modulus
  /* x10 = rptr_limb_mod = &w3 */
  li        x10, 3
  /* x11 = rptr_limb_buf = &w2 */
  li        x11, 2


  /* clear flags */
  bn.add    w31, w31, w31
  /* init buffer with R - m
     buf = w[5+N-1:5] <= R - m = unsigned(0 - m) */

  loop      x30, 3
    bn.lid    x10, 0(x16++)
    bn.subb   w3, w31, w3
    bn.movr   x8++, x10

  /* Compute R^2 mod M = R*2^(N*w) mod M.
     R^2 mod M can be computed by performing N*w duplications of R,
     interleaved with conditional subtractions of modulus. Modulus is
     subtracted if dobiling result is greater than modulus, i.e. either
     there was a final carry at the end of the doubling procedure or the lower
     N*w bits of the result are greater than the modulus. */
  loop      x24, 27

    /* Duplicate the intermediate bigint result. This can overflow such that
       bit 2^(N*w) (represented by the carry flag after final loop cycle)
       is set. */
    li        x8, 5
    bn.add    w31, w31, w31, FG1
    loop      x30, 3
      bn.movr   x11, x8
      bn.addc   w2, w2, w2, FG1
      bn.movr   x8++, x11

    /* In case of final carry in doubling procedure substract modulus */
    /* Jump to 'rr_sub' if FG1.C == 1 */
    csrrs     x3, FG1, x0
    andi      x3, x3, 1
    bne       x3, x0, rr_sub

    /* In case there was no final carry in the addition, we have to check
       wether the N*w sized bigint w/o carry is greater than the modulus. */
    bn.lid    x10, 0(x17)
    bn.movr   x11, x9
    bn.cmp    w2, w3, FG1
    csrrs     x3, FG1, x0

    /* If the highest limbs of buf and mod are equal we have to run a
       multi-limb comparison. This is very unlikely to happen. If this
       verification is not used with keys where this situation occurs, the
       following 3 lines and (if not needed elsewhere) the compare routine
       can be removed. */
    andi      x5, x3, 8
    beq       x5, x0, rr_cmp
    jal       x1, cmp_dmem_reg_buf

    /* if m > r: jump to end_loop (without subtraction) */
    rr_cmp:
    andi      x5, x3, 1
    bne       x5, x0, rr_end_loop

    /* subtract modulus from current buffer
       buf = w[5+N-1:5] <= buf - m */
    rr_sub:
    li        x8, 5
    addi      x16, x22, 0
    bn.add    w31, w31, w31, FG1
    loop      x30, 4
      bn.lid    x10, 0(x16++)
      bn.movr   x11, x8
      bn.subb   w3, w2, w3, FG1
      bn.movr   x8++, x10

    rr_end_loop:
      nop

  /* store computed RR in dmem
     [dmem[dptr_RR+N*32-1]:dmem[dptr_RR]] <= buf = w[5+N-1:5] */
  li        x8, 5
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
 * Main loop body for variable-time Montgomery Modular Multiplication
 *
 * Returns: C <= (C + A*b_i + M*m0'*(C[0] + A[0]*b_i))/(2^WLEN) mod R
 *
 * This implements the main loop body for the Montgomery Modular Multiplication
 * as well as the conditional subtraction. See e.g. Handbook of Applied
 * Cryptography (HAC) 14.36 (steps 2.1 and 2.2) and step 3.
 * This subroutine has to be called for every iteration of the loop in step 2
 * of HAC 14.36, i.e. once per limb of operand B (x in HAC notation). The limb
 * is supplied via w2. In the comments below, the index i refers to the
 * i_th call to this subroutine within one full Montgomery Multiplication run.
 * Step 3 of HAC 14.36 is replaced by the approach to perform the conditional
 * subtraction when the intermediate result is larger than R instead of m. See
 * e.g. https://eprint.iacr.org/2017/1057 section 2.4.2 for a justification.
 * This does not omit the conditional subtraction.
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


  /* With the computation of u_i, the compuations for a cycle 0 for the loop
     below are already partly done. The following instructions (until the
     start of the loop) implement the remaining steps, such that cylce 0 can be
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
       the j_th limb of the buffer A, A[j] arre added to the multiplication
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

  /* No subtracion if carry bit of addition of carry words not set. */
  csrrs     x2, FG1, x0
  andi      x2, x2, 1
  beq       x2, x0, mont_loop_no_sub

  /* limb-wise subtraction */
  li        x12, 30
  li        x13, 24
  addi      x16, x22, 0
  li        x8, 4
  loop      x30, 4
    bn.lid    x13, 0(x16++)
    bn.movr   x12, x8
    bn.subb   w24, w30, w24
    bn.movr   x8++, x13


  mont_loop_no_sub:

  /* restore pointers */
  li        x8, 4
  li        x10, 4

  ret


/**
 * Variable-time Montgomery Modular Multiplication
 *
 * Returns: C = montmul(A,B) = A*B*R^(-1) mod M
 *
 * This implements the limb-by-limb interleadved Montgomory Modular
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
 * clobbered registers: x5, x6, x7, x8, x10, x12, x13, x17, x19, x20, x21
 *                      w2, w3, w24 to w30, w4 to w[4+N-1]
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
    addi      x6, x16, 0
    addi      x7, x19, 0

    /* Main loop body of Montgomory Multiplication algorithm */
    jal       x1, mont_loop

    /* restore regs */
    addi      x16, x6, 0
    addi      x19, x7, 0

  /* restore pointers */
  li        x8, 4
  li        x10, 4

  ret


/**
 * Variable time modular exponentiation with exponent of the form e=2^e'+1
 *
 * Returns: C = modexp(A,2^e'+1) = A^(2^e'+1) mod M
 *
 * This implements the square and multiply algorithm for exponents of the
 * form e=2^e'+1. Thus, the routine can be used for exponentiation with Fermat
 * primes (by setting e'=16 for e=F4=65537 and e'=1 for e=F0=3).
 *
 * The squared Montgomery modulus RR and the Montgomery constant m0' have to
 * be precomputed and provided at the appropriate locations in dmem.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * The base bignum A is expected in the input buffer, the result C is written
 * to the output buffer. Note, that the content of the input buffer is
 * modified during execution.
 *
 * @param[in]  dmem[0] e': number for exponent derivation (e = 2^e+1)
 * @param[in]  dmem[4] N: Number of limbs per bignum
 * @param[in]  dmem[8] dptr_m0inv: pointer to m0' in dmem
 * @param[in]  dmem[12] dptr_rr: pointer to RR in dmem
 * @param[in]  dmem[16] dptr_m: pointer to first limb of modulus M in dmem
 * @param[in]  dmem[20] dptr_sig: pointer to signature in dmem
 * @param[in]  dmem[28] dptr_out: pointer to recovered message
 *
 * clobbered registers: x2, x5 to x13, x16 to x21, x29, x30, x31
                        w2, w3, w24 to w31, w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
modexp_var:
  /* prepare all-zero reg */
  bn.xor    w31, w31, w31

  /* load number of limbs (x30 <= N; x31 = N-1 <= N1) */
  lw        x30, 4(x0)
  addi      x31, x30, -1

  /* load pointer to modulus (x16 <= dptr_m) */
  lw        x16, 16(x0)

  /* load pointer to m0' (x17 <= dptr_m0inv)*/
  lw        x17, 8(x0)

  /* load pointer to RR (x18 <= dptr_rr) */
  lw        x18, 12(x0)

  /* load exponent (x29 <= e') */
  lw        x29, 0(x0)

  /* Compute Montgomery constants and reload clobbered pointers */
  jal       x1, compute_m0inv
  jal       x1, compute_rr
  lw        x16, 16(x0)
  lw        x17, 8(x0)
  lw        x18, 12(x0)

  /* prepare pointers to temp regs */
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  /* convert signature to Montgomery domain
     out_buf = *x28 = *dmem[28]
         <= montmul(*x19, *x20) = montmul(*dptr_sig, *dptr_rr) = sig*R mod M */
  lw        x19, 20(x0)
  lw        x20, 12(x0)
  lw        x21, 28(x0)
  jal       x1, montmul
  /* store result in dmem starting at dmem[dptr_out] */
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* 16 consecutive Montgomery squares on the outbut buffer, i.e. after loop:
     out_buf <= out_buf^65536*R mod M */
  loop      x29, 8
    /* out_buf  = *x28 = *dmem[28]
               <= montmul(*x28, *x20) = montmul(*dptr_out, *dptr_out)
                = out_buf^2*R mod M */
    lw        x19, 28(x0)
    lw        x20, 28(x0)
    lw        x21, 28(x0)
    jal       x1, montmul
    /* Store result in dmem starting at dmem[dptr_out] */
    loop      x30, 2
      bn.sid    x8, 0(x21++)
      addi      x8, x8, 1
    nop

  /* final multiplication and conversion of result from Montgomery domain
     out_buf  = *x28 = *dmem[28]
             <= montmul(*x28, *x20) = montmul(*dptr_sig, *dptr_out)
              = out_buf*sig/R mod M = sig^65537 mod M */
  lw        x19, 20(x0)
  lw        x20, 28(x0)
  lw        x21, 28(x0)
  jal       x1, montmul

  /* Final conditional subtraction of modulus if mod >= out_buf. This could
     be done in variable time, but for the sake of reduced code we use a loop
     with N cycles. */
  bn.add    w31, w31, w31
  li        x17, 16
  loop      x30, 4
    bn.movr   x11, x8++
    bn.lid    x9, 0(x16++)
    bn.subb   w2, w2, w3
    bn.movr   x17++, x11
  csrrs     x2, FG0, x0
  /* TODO: currently we subtract the modulus if out_buf == M. This should
            never happen in an RSA context. We could catch this and raise an
            alert. */
  andi      x2, x2, 1
  li        x8, 4
  bne       x2, x0, no_sub
  li        x8, 16
  no_sub:

   /* store result in dmem starting at dmem[dptr_out] */
  lw        x21, 28(x0)
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  ret
