/* Copyright lowRISC Contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 *
 * Derived from code in
 * https://chromium.googlesource.com/chromiumos/platform/ec/+/refs/heads/cr50_stab/chip/g/dcrypto/dcrypto_bn.c
 *
 * The interface for this file can be accessed through the following symbols.
 * All of them are declared weak in this file, so can be overridden by code
 * that links against this object:
 *
 *   out_buf:  OUTPUT
 *             384 bytes
 *             The resulting recovered message
 *
 *   in_mod:   INPUT
 *             384 bytes
 *             The modulus
 *
 *   in_buf:   INPUT
 *             384 bytes
 *             The signature
 *
 *   in_rr:    INPUT
 *             384 bytes
 *             The Montgomery transformation constant R^2 = (2^3072)^2 mod N
 *
 *   in_m0inv: INPUT
 *             384 bytes
 *             The Montgomery constant
 */

.text

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
 * Main loop body for variable-time 3072-bit Montgomery Modular Multiplication
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
  loopi     11, 14
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
  csrrs     x2, 0x7c1, x0
  andi      x2, x2, 1
  beq       x2, x0, mont_loop_no_sub

  /* limb-wise subtraction */
  li        x12, 30
  li        x13, 24
  addi      x16, x22, 0
  li        x8, 4
  loopi     12, 4
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
 * Variable-time 3072-bit Montgomery Modular Multiplication
 *
 * Returns: C = montmul(A,B) = A*B*R^(-1) mod M
 *
 * This implements the limb-by-limb interleadved Montgomory Modular
 * Multiplication Algorithm. This is only a wrapper around the main loop body.
 * For algorithmic implementation details see the mont_loop subroutine.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dptr_M, dmem pointer to first limb of modulus M
 * @param[in]  x17: dptr_m0d, dmem pointer to Montgomery Constant m0'
 * @param[in]  x19: dptr_a, dmem pointer to first limb of operand A
 * @param[in]  x20: dptr_b, dmem pointer to first limb of operand B
 * @param[in]  w31: all-zero
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[out] [w15:w4]: result C
 *
 * clobbered registers: x5, x6, x7, x8, x10, x12, x13, x17, x19, x20, x21
 *                      w2, to w15, w24 to w30
 * clobbered Flag Groups: FG0, FG1
 */
montmul:
  /* load Montgomery constant: w3 = dmem[x17] = dmem[dptr_m0d] = m0' */
  bn.lid    x9, 0(x17)

  /* init regfile bigint buffer with zeros */
  bn.mov    w2, w31
  loopi     12, 1
    bn.movr   x10++, x11

  /* iterate over limbs of operand B */
  loopi     12, 8

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
 * Variable time 3072-bit modular exponentiation with exponent 65537
 *
 * Returns: C = modexp(A,65537) = mod M
 *
 * This implements the square and multiply algorithm for the
 * F4 exponent (65537).
 *
 * The squared Montgomery modulus RR and the Montgomery constant m0' have to
 * be provided at the appropriate locations in dmem.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * The base bignum A is expected in the input buffer, the result C is written
 * to the output buffer. Note, that the content of the input buffer is
 * modified during execution.
 *
 * @param[in]  dmem[in_m0inv] pointer to m0' in dmem
 * @param[in]  dmem[in_rr] pointer to RR in dmem
 * @param[in]  dmem[in_mod] pointer to first limb of modulus M in dmem
 * @param[in]  dmem[in_buf] pointer to buffer with base bignum
 * @param[in]  dmem[out_buf] pointer to output buffer
 *
 * clobbered registers: x2, x5 to x13, x16 to x21, x29
                        w2, to w15, w24 to w31
 * clobbered Flag Groups: FG0, FG1
 */
 .globl modexp_var_3072_f4
modexp_var_3072_f4:
  /* prepare all-zero reg */
  bn.xor    w31, w31, w31

  /* prepare pointers to temp regs */
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  /* set pointers to buffers */
  la        x24, out_buf
  la        x16, in_mod
  la        x23, in_buf
  la        x26, in_rr
  la        x17, in_m0inv

  /* convert input to Montgomery domain and store in dmem
     dmem[out_buf] = montmul(dmem[in_buf], dmem[in_RR]) = A*R mod M */
  addi      x19, x23, 0
  addi      x20, x26, 0
  addi      x21, x24, 0
  jal       x1, montmul
  loopi     12, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* 16 consecutive Montgomery squares on the outbut buffer, i.e. after loop:
     dmem[out_buf] <= dmem[out_buf]^65536*R mod M */
  loopi     16, 8
    /* dmem[out_buf]  = montmul(dmem[out_buf], dmem[out_buf]) */
    addi      x19, x24, 0
    addi      x20, x24, 0
    addi      x21, x24, 0
    jal       x1, montmul
    loopi     12, 2
      bn.sid    x8, 0(x21++)
      addi      x8, x8, 1
    nop

  /* final multiplication and conversion of result from Montgomery domain
     out_buf  <= montmul(*x28, *x20) = montmul(dmem[in_buf], dmem[out_buf]) */
  addi      x19, x23, 0
  addi      x20, x24, 0
  addi      x21, x24, 0
  jal       x1, montmul

  /* Final conditional subtraction of modulus if mod >= dmem[out_buf]. */
  bn.add    w31, w31, w31
  li        x17, 16
  loopi     12, 4
    bn.movr   x11, x8++
    bn.lid    x9, 0(x16++)
    bn.subb   w2, w2, w3
    bn.movr   x17++, x11
  csrrs     x2, 0x7c0, x0
  /* TODO: currently we subtract the modulus if out_buf == M. This should
            never happen in an RSA context. We could catch this and raise an
            alert. */
  andi      x2, x2, 1
  li        x8, 4
  bne       x2, x0, no_sub
  li        x8, 16

  no_sub:

  /* store result in output buffer */
  addi      x21, x24, 0
  loopi     12, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  ret

/**
 * Subtracts the modulus M from A.
 *
 * Flags: After this subroutine, the C flag is set to 1 if the subtraction
 * underflowed.
 *
 * This routine runs in variable time.
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  [w4:w15]: operand A
 * @param[in]  w31: all-zero
 * @param[out] [w16:w27]: result
 *
 * clobbered registers: x8 to x12, w2, w3, w16 to w27
 * clobbered Flag Groups: FG0
 */
subtract_modulus_var:

  /* Prepare temporary registers. */
  li        x8, 4
  li        x9, 2
  li        x10, 3
  li        x11, 16

  /* Copy pointer to modulus. */
  addi      x12, x16, 0

  /* Clear flags. */
  bn.add    w31, w31, w31

  /* Subtract M from A. */
  loopi     12, 4
    /* w2 <= A[i] */
    bn.movr   x9, x8++
    /* w3 <= M[i] */
    bn.lid    x10, 0(x12++)
    /* w2 <= w2 - w3 */
    bn.subb   w2, w2, w3
    /* out[i] <= w2 */
    bn.movr   x11++, x9

  ret

/**
 * Doubles a number and reduces modulo M in-place.
 *
 *   Returns: C = (A + A) mod M
 *
 * Requires that A < M < 2^3072. Writes output to the A buffer in DMEM. This
 * routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  [w4:w15]: operand A
 * @param[in]  w31: all-zero
 * @param[out] [w4:w15]: result C
 *
 * clobbered registers: x2, x3, x7 to x12, w2 to w27
 * clobbered Flag Groups: FG0
 */
double_mod_var:
  /* Save copy of pointer to modulus. */
  addi      x12, x16, 0

  /* Clear flags. */
  bn.add    w31, w31, w31

  /* Compute aa=(A + A).
       [w4:w15] <= (A+A) mod 2^3072 = aa[0:3071]*/
  li        x9, 2
  li        x10, 4
  loopi     12, 3
    /* w2 <= a[i] */
    bn.movr   x9, x10
    /* w2 <= w2 + w2 */
    bn.addc   w2, w2, w2
    /* aa[i] <= w2 */
    bn.movr   x10++, x9

  /* Extract final carry bit from flags register.
       x2 <= aa[3072] */
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1

  jal       x1, subtract_modulus_var

  /* Extract final borrow bit from flags register. */
  csrrs     x3, 0x7c0, x0
  andi      x3, x3, 1

  /**
   * Select either aa or aa' based on carry/borrow bits.
   *
   * If aa < M, it follows that the carry bit aa[3072] = 0 (since M < 2^3072).
   * It also follows that the borrow from subtracting M must be 1. In this
   * case, select aa; otherwise, select aa-M.
   */

  /* x2 <= (!x2) & x3 */
  xori      x2, x2, 1
  and       x2, x2, x3

  /* Select aa if x2 = 0, otherwise aa-M. */
  bne       x2, x0, sel_aa

  /* Copy subtraction result to w4:w15. */
  li        x8, 4
  li        x11, 16
  loopi     12, 2
    bn.movr   x8, x11++
    addi      x8, x8, 1

sel_aa:

  ret

/**
 * Computes the R^2 Montgomery constant and stores it in DMEM.
 *
 *   Returns RR = (2^3072)^2 mod M
 *
 * This implementation is based on section 2.3 of "Montgomery Arithmetic from a
 * Software Perspective" (https://eprint.iacr.org/2017/1057). For the purposes
 * of RSA 3072, the parameters w and n from the paper are fixed (w=256, n=12).
 *
 * The algorithm from the paper assumes that 2^wn-1 <= M < 2^wn; we lightly
 * adapt the implementation to accept any positive M by subtracting M from c0
 * until c0 < M.
 *
 * The result is stored in dmem[in_rr]. This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[in_mod] pointer to first limb of modulus M in dmem
 *
 * clobbered registers: x2, x3, x7 to x11, x16, w2 to w27, w31
 * clobbered Flag Groups: FG0
 */
 .globl precomp_rr
precomp_rr:
  /* Prepare all-zero register. */
  bn.xor    w31, w31, w31

  /* Set pointer to modulus. */
  la        x16, in_mod

  /* Zero [w4:w15]. */
  li        x9, 4
  li        x10, 31
  loopi     12, 1
    bn.movr   x9++, x10

  /* w16 <= 1 */
  bn.addi   w16, w31, 1

  /* Initialize c0
     c0 = [w4:w15] <= [w4:w16] >> 1 = 2^3701 */
  bn.rshi   w15, w16, w15 >> 1


precomp_rr_sub_start:

  /* Repeatedly subtract M until c0 < M.
       [w16:w27] <= (c0 - M) */
  jal       x1, subtract_modulus_var

  /* Extract borrow bit from flags register. */
  csrrs     x2, 0x7c0, x0
  andi      x2, x2, 1

  /* If borrow is set, then subtraction underflowed, meaning c0 < M; done. */
  bne       x2, x0, precomp_rr_sub_done

  /* If we got here, then c0 > M; set c0 = c0 - M and repeat.
       c0 = [w4:w15] <= [w16:w27] = c0 - M */
  li        x8, 4
  li        x11, 16
  loopi     12, 2
    bn.movr   x8, x11++
    addi      x8, x8, 1

  /* Jump back to start of subtractions. */
  beq       x0, x0, precomp_rr_sub_start

precomp_rr_sub_done:

  /* Now, we know that c0 = [w4:w15] = (2^3071) mod M. */

  /* One modular doubling to get c1 \equiv 2^3072 mod M.
     c1 = [w4:w15] <= ([w4:w15] * 2) mod M = (2^3072) mod M */
  jal     x1, double_mod_var

  /* Compute (2^3072)^2 mod M by performing 3072 modular doublings.
     Loop is nested only because #iterations must be < 1024 */
  loopi     12, 4
    loopi     256, 2
      jal     x1, double_mod_var
      /* Nop because inner loopi can't end on a jump instruction. */
      nop
    /* Nop because outer loopi can't end on a loop instruction. */
    nop

  /* Store result in dmem[in_rr]. */
  li        x9, 4
  la        x26, in_rr
  loopi     12, 2
    bn.sid    x9, 0(x26++)
    addi      x9, x9, 1

  ret

/**
 * Computes least significant 256 bits of a 256x256 bit product.
 *
 * Returns c = (a x b) mod (2^256).
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in] w2: a, first operand
 * @param[in] w5: b, second operand
 * @param[out] w27: c, result
 *
 * clobbered registers: w27
 * clobbered flag groups: FG0
 */
mul256_low_w2xw5:
  bn.mulqacc.z          w2.0, w5.0,  0
  bn.mulqacc            w2.1, w5.0, 64
  bn.mulqacc.so  w27.L, w2.0, w5.1, 64
  bn.mulqacc            w2.2, w5.0,  0
  bn.mulqacc            w2.1, w5.1,  0
  bn.mulqacc            w2.0, w5.2,  0
  bn.mulqacc            w2.3, w5.0, 64
  bn.mulqacc            w2.2, w5.1, 64
  bn.mulqacc            w2.1, w5.2, 64
  bn.mulqacc.so  w27.U, w2.0, w5.3, 64

  ret

/**
 * Checks whether two wide registers have equal values.
 *
 *   Returns c = 1 if a = b, 0 otherwise.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  w6: a, first operand
 * @param[in]  w27: b, second operand
 * @param[out] x4: c, result
 *
 * clobbered registers: x3, x4
 * clobbered Flag Groups: FG0
 *
 */
check_eq_w6w27:
    /* Check if b < a. */
    bn.cmp    w27, w6

    /* Get value from flag register.
         x3 <= (b < a) */
    csrrs     x3, 0x7c0, x0
    andi      x3, x3, 1

    /* Check if a < b. */
    bn.cmp    w6, w27

    /* Get value from flag register.
         x4 <= (a < b) */
    csrrs     x4, 0x7c0, x0
    andi      x4, x4, 1

    /* If b < a or a < b, then a != b; otherwise a = b.
         x4 <= !(b < a | a < b) = (a == b)*/
    or        x4, x4, x3
    xori      x4, x4, 1

    ret

/**
 * Computes the m0_inv Montgomery constant and stores it in DMEM.
 *
 *   Returns m0_inv = (- M') mod (2^256)
 *                    where M' is the modular multiplicative inverse of M.
 *
 * This implementation is based on ALgorithm 3 of "Montgomery Arithmetic from a
 * Software Perspective" (https://eprint.iacr.org/2017/1057). For the purposes
 * of RSA 3072, the parameters w and n from the paper are fixed (w=256, n=12).
 *
 * The result is stored in dmem[in_m0inv]. This routine runs in variable time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[in_mod] pointer to first limb of modulus M in dmem
 *
 * clobbered registers: x2 to x4, x9, x16, x26, w2 to w6, w27, w31
 * clobbered Flag Groups: FG0
 */
 .globl precomp_m0_inv
precomp_m0_inv:
  /* Prepare all-zero register. */
  bn.xor    w31, w31, w31

  /* y = w2 <= 1 */
  bn.addi   w2, w31, 1

  /* i = x2 <= 1 */
  addi   x2, x0, 1

  /* pow2i = w3 <= 2^i = 2 */
  bn.addi   w3, w31, 2

  /* maski = w4 <= 2^(i+1) - 1 = 3 */
  bn.addi   w4, w31, 3

  /* w5 <= M[0] = M mod (2^256) */
  li        x3, 5
  la        x16, in_mod
  bn.lid    x3, 0(x16)

  /* w6 <= 1 */
  bn.addi   w6, w31, 1

  /**
   * Main loop from i=1 to i=255.
   *
   * Invariants:
   *   x2 = i
   *   w2 = y
   *   w3 = 2^i (powi)
   *   w4 = 2^(i+1)-1 (maski)
   *   w5 = M[0] (constant)
   *   w6 = 1    (constant)
   *   y < 2^i
   */
  loopi 255, 8
    /* w27 <= (w2 * w5) mod (2^256)
            = (y * M[0]) mod (2^256) = (M * y) mod (2^256) */
    jal       x1, mul256_low_w2xw5
    /* w27 <= w27 & maski = (M * y) mod (2^(i+1)) */
    bn.and    w27, w27, w4
    /* x4 <= 1 if w27 = 1, 0 otherwise */
    jal       x1, check_eq_w6w27
    /* skip addition if w27 == 1*/
    bne       x4, x0, skip_add
    /* y = w2 <= y + pow2i */
    bn.add    w2, w2, w3
    skip_add:
    /* i = x2 <= i + 1 */
    addi      x2, x2, 1
    /* pow2i = w3 <= pow2i * 2 = 2^i */
    bn.add    w3, w3, w3
    /* maski = w4 <= maski + pow2i = 2^(i+1) - 1 */
    bn.add    w4, w4, w3

  /* m0_inv = w2 <= 2^256 - y = (0 - y) mod 2^256  */
  bn.sub    w2, w31, w2

  /* Store result in dmem[in_m0inv]. */
  li        x9, 2
  la        x26, in_m0inv
  bn.sid    x9, 0(x26)

  ret

/* Output buffer for the resulting, recovered message. */
.section .data.out_buf
.weak out_buf
out_buf:
  .zero 384

/* Input buffer for the modulus. */
.section .data.in_mod
.weak in_mod
in_mod:
  .zero 384

/* Input buffer for the signature. */
.section .data.in_buf
.weak in_buf
in_buf:
  .zero 384

/* Input buffer for the Montgomery transformation constant R^2. */
.section .data.in_rr
.weak in_rr
in_rr:
  .zero 384

/* The Montgomery constant. */
.section .data.in_m0inv
.weak in_m0inv
in_m0inv:
  .zero 32
