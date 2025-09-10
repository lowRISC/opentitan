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
 * Constant-time, conditional swap of two general-purpose registers
 *
 * This routine implements a conditional, constant-time, out-of-place swap of
 * two values in GPR registers such that
 *
 * Input:  GPR0(X), GPR1(Y)
 * Output: GPR2(Y), GPR3(X) if b == 0 else GPR2(X), GPR3(Y)
 *
 * It is a direct adaption of the masked conditional swap presented in
 *
 *   https://ieeexplore.ieee.org/document/9581247
 *
 * @param[in]  x23: GPR0 containing value X
 * @param[in]  x24: GPR1 containing value Y
 * @param[in]  x14: a conditional bit b
 * @param[out] x19: GPR2 containing either X or Y depending on b
 * @param[out] x20: GPR3 containing either X or Y depending on b
 *
 * Clobbered registers: x17, x18
 */
cond_swap_gprs:
  /*
   * Calculate Boolean mask (0 - b) = 0 if b == 0 else 0xFFFF_FFFF
   * Randomize the destination register to soften the impact of overwritting
   * it with all 0s or all 1s:
   *
   *   d = (0 - b)
   */
  csrrs x17, RND, x0
  sub   x17, x0, x14

  /* z = (X ^ Y) & d. */
  xor x18, x23, x24
  and x18, x17, x18

  /* Sample a random mask r and XOR it to the intermediate result: z = z ^ r. */
  csrrs x17, RND, x0
  xor x18, x17, x18

  /*
   * Calculate the value of the output registers:
   *
   *   GPR2 = (z ^ X) ^ r
   *   GPR3 = (z ^ Y) ^ r
   */
  xor x19, x18, x23
  xor x19, x17, x19
  xor x20, x18, x24
  xor x20, x17, x20

  ret

/**
 * Constant-time, boolean-masked Montgomery ladder bigint exponentiation
 *
 * Calculates: C = modexp(A, E) = A^E mod M
 *
 * This routine implements a constant-time modular exponentation Montgomery
 * ladder using Boolean-masked exponents in two shares (d0, d1) as proposed by
 * Tunstall et al.
 *
 *   [1] https://eprint.iacr.org/2018/1226.pdf
 *
 * The individual bits of the exponent shares randomize the memory accesses of
 * intermediate values in each iteration thus inhibiting horizontal attacks that
 * exploit leakage spanning multiple rounds. As the exponent is re-masked for
 * every exponentation vertical attacks over multiple traces are mitigated as
 * well.
 *
 * TODO: The actual intermediate values are not randomized requiring an
 * additional blinding of the input. An efficient, inverse-free technique
 * was proposed by Ebeid and Lambert:
 *
 *   [2] https://dl.acm.org/doi/10.1145/1873548.1873556
 *
 * The computation is carried out in the Montgomery domain, by using the montmul
 * primitive. The squared Montgomery modulus RR and the Montgomery constant m0'
 * have to be precomputed and provided at the appropriate locations in DMEM.
 *
 * @param[in] x23: dptr_r0, DMEM pointer to the input A and output C
 * @param[in] x24: dptr_r1, DMEM pointer to a tmp location of size 512 bytes
 * @param[in] x25: dptr_r2, DMEM pointer to a tmp location of size 512 bytes
 * @param[in] x26: dptr_d0, DMEM pointer to the first share of exponent d
 * @param[in] x27: dptr_d1, DMEM pointer to the second shrare of the exponent d
 * @param[in] x28: dptr_n,  DMEM pointer to the modulus M
 * @param[in] x29: dptr_rr, DMEM pointer to RR = R^2 mod M
 * @param[in] x30: N, number of limbs per bignum
 * @param[in]  w1: Montgomery Constant m0'
 * @param[in] w31: all-zero
 *
 * The buffers A, r0, r1, r2, d0 and d1 are modified over the course of this
 * routine.
 *
 * Clobbered registers: x5 to x22, x31
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * Clobbered flag groups: FG0, FG1
 */
modexp:
  /* Constant wide register pointers */
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  /* Compute (N-1): x31 <= x30 - 1 = N - 1 */
  addi      x31, x30, -1

  /*
   * Convert input to Montgomery domain:
   *
   *   [w[4+N-1]:w4] = A' = modexp(A, RR)
   */
  addi      x16, x28, 0
  addi      x19, x23, 0
  addi      x20, x29, 0
  jal       x1, montmul

  /* montmul clobbers the flags, clear them here. */
  bn.add w31, w31, w31, FG0
  bn.add w31, w31, w31, FG1

  /*
   * Step 1 in Algorithm 2 [1]:
   *
   * Initialize r0 and r1 with -M mod R. Note that this Montgomery ladder
   * operates with redundant residuals over Z/RZ as opposed to Z/MZ which
   * significantly simplifies the final comparison step in the Montgomery
   * multiplication. Only the in the very last step of the exponentational, when
   * the output is converted back from the Montgomery form, the value is mapped
   * into Z/NZ (see Section 2.4.2 in https://eprint.iacr.org/2017/1057.pdf for
   * more details on this optimization).
   *
   * [1] asks for r0 and r1 to be initialzed to 1 or montmul(1, RR) in the
   * Montgomery domain over Z/MZ which congruent to -M in Z/RZ.
   */
  addi x2, x23, 0
  addi x3, x24, 0
  addi x5, x28, 0
  loop x30, 5
    bn.lid  x11, 0(x5++)
    bn.subb w2, w31, w2
    bn.sid  x11, 0(x2++)
    bn.sid  x11, 0(x3++)

  /*
   * Step 2 in Algorithm 2 [1]:
   *
   * Generate a random bit x4 = b'.
   */
  csrrs   x4, RND, x0
  andi    x4, x4, 1

  /* Store the converted input back into DMEM r[b' ^ 1] = A'. */
  xori x14, x4, 1
  jal x1, cond_swap_gprs

  addi x2, x8, 0
  loop x30, 2
    bn.sid  x2, 0(x19++)
    addi x2, x2, 1

  /* Compute bit length of current bigint size. */
  slli      x21, x30, 8

  /*
   * Main loop of the exponentiation, iterate over all exponent bits:
   *
   * w2, x2, x3, x4 hold secret values for all the iterations. x2, x3 are shares
   * of the same secret.
   */
  loop      x21, 42

    /* Shift d0 and siphon the shifted out MSB into FG0, x3 = a[i] = d0[i]. */
    addi      x15, x26, 0
    loop      x30, 3
      bn.lid    x11, 0(x15)
      /* w2 <= w2 << 1 */
      bn.addc   w2, w2, w2
      bn.sid    x11, 0(x15++)
    csrrs x3, FG0, x0
    andi x3, x3, 1

    /*
     * Step 4 in Algorithm 2 [1]:
     *
     * Depending on a[i] assign the input buffers to calculate
     * [w[4+N-1]:w4] = r[a[i]] * r[a[i] ^ 1] and store the result in r2.
     */
    addi x14, x3, 0
    jal x1, cond_swap_gprs

    addi x16, x28, 0
    jal x1, montmul

    addi x2, x8, 0
    addi x15, x25, 0
    loop x30, 2
      bn.sid  x2, 0(x15++)
      addi x2, x2, 1

    /* Shift d1 and siphon the shifted out MSB into FG0, x2 = b[i] = d1[i]. */
    addi      x15, x27, 0
    loop      x30, 3
      bn.lid    x11, 0(x15)
      /* w2 <= w2 << 1 */
      bn.addc   w2, w2, w2
      bn.sid    x11, 0(x15++)
    csrrs x2, FG0, x0
    andi  x2, x2, 1

    /* Calculate c = (b[i] ^ b') ^ a[i] = (x2 ^ x4) ^ x3. */
    xor x4, x2, x4
    xor x4, x4, x3

    /*
     * Step 5 in Algorithm 2 [1]:
     *
     * Calculate [w[4+N-1]:w4] = r[c] * r[c].
     */
    addi x14, x4, 0
    jal x1, cond_swap_gprs

    addi x16, x28, 0
    addi x20, x19, 0
    jal x1, montmul

    /*
     * Step 7 in Algorithm 2 [1]:
     *
     * b' = b[i] = x2
     */
    addi x4, x2, 0

    /*
     * Step 6 in Algorithm 2 [1]:
     *
     * Store r2 and r[c] * r[c] into DMEM depending on b[i].
     */
    addi x14, x3, 0
    jal x1, cond_swap_gprs

    addi x2, x8, 0
    loop x30, 2
      bn.sid  x2, 0(x19++)
      addi x2, x2, 1

    addi x16, x25, 0
    loop x30, 2
      bn.lid x11, 0(x16++)
      bn.sid x11, 0(x20++)

    nop

  /* Make sure the output C is in r0. */
  addi x14, x4, 0
  jal x1, cond_swap_gprs

  /* Convert back from Montogomery form. */
  addi x16, x28, 0
  addi x21, x23, 0
  jal x1, montmul_mul1

  ret

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
 * The base bignum A is expected in the input buffer, the result C is written
 * to the output buffer. Note, that the content of the input buffer is
 * modified during execution.
 *
 * @param[in]   x2: dptr_c, dmem pointer to buffer for output C
 * @param[in]  x14: dptr_a, dmem pointer to first linb of input A
 * @param[in]  x16: dptr_M, dmem pointer to first limb of modulus M
 * @param[in]  x18: dptr_RR, dmem pointer to Montgmery constant RR
 * @param[in]  x30: N, number of limbs per bignum
 * @param[in]   w1: Montgomery Constant m0'
 * @param[in]  w31: all-zero
 * @param[out] dmem[dptr_c:dptr_c+N*32] C, A^65537 mod M
 *
 * clobbered registers: x3 to x13, x16 to x31
 *                      w0 to w3, w24 to w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
modexp_65537:
  /* prepare pointers to temp regs */
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  /* Compute (N-1).
       x31 <= x30 - 1 = N - 1 */
  addi      x31, x30, -1

  /* convert to montgomery domain montmul(A,RR)
  in = montmul(A,RR) montmul(A,RR) = C*R mod M */
  addi      x19, x14, 0
  addi      x20, x18, 0
  addi      x21, x14, 0
  jal       x1, montmul
  /* Store result in dmem starting at dmem[dptr_a] */
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* pointer to out buffer */
  addi      x21, x2, 0

  /* zeroize w2 and reset flags */
  bn.sub    w2, w2, w2

  /* pointer to modulus */
  addi      x3, x16, 0

  /* this loop initializes the output buffer with -M */
  loop      x30, 3
    /* load limb from modulus */
    bn.lid    x11, 0(x3++)

    /* subtract limb from 0 */
    bn.subb   w2, w31, w2

    /* store limb in dmem */
    bn.sid    x11, 0(x21++)

  /* TODO: Is this squaring necessary? */
  /* 65537 = 0b10000000000000001
               ^ sqr + mult
    out = montmul(out,out)       */
  addi      x19, x2, 0
  addi      x20, x2, 0
  jal       x1, montmul
  /* Store result in dmem starting at dmem[dptr_c] */
  addi      x21, x2, 0
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* out = montmul(in,out)       */
  addi      x19, x14, 0
  addi      x20, x2, 0
  jal       x1, montmul

  /* store multiplication result in output buffer */
  addi      x21, x2, 0
  li        x8, 4
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* 65537 = 0b10000000000000001
                ^<< 16 x sqr >>^   */
  loopi      16, 8
    /* square: out = montmul(out, out) */
    addi      x19, x2, 0
    addi      x20, x2, 0
    jal       x1, montmul
    /* Store result in dmem starting at dmem[dptr_c] */
    addi      x21, x2, 0
    loop      x30, 2
      bn.sid    x8, 0(x21++)
      addi      x8, x8, 1
    nop

  /* 65537 = 0b10000000000000001
                          mult ^
     out = montmul(in,out)       */
  addi      x19, x14, 0
  addi      x20, x2, 0
  jal       x1, montmul

  /* store multiplication result in output buffer */
  addi      x21, x2, 0
  li        x8, 4
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* convert back from montgomery domain */
  /* out = montmul(out,1) = out/R mod M  */
  addi      x19, x2, 0
  addi      x21, x2, 0
  jal       x1, montmul_mul1

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
cond_sub_to_dmem:
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
 * This implements the limb-by-limb interleaved Montgomery Modular
 * Multiplication Algorithm, with one operand fixed to 1. This is only a
 * wrapper around the main loop body. For algorithmic implementation details
 * see the mont_loop subroutine.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * @param[in]  x16: dmem pointer to first limb of modulus M
 * @param[in]  x19: dmem pointer to first limb of operand A
 * @param[in]  x21: dmem pointer to first limb of result C
 * @param[in]  x30: N, number of limbs
 * @param[in]  x31: N-1, number of limbs minus one
 * @param[in]   x8: pointer to temp reg, must be set to 4
 * @param[in]   x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[in]   w1: Montgomery Constant m0'
 * @param[in]  w31: all-zero
 *
 * clobbered registers: x6, x7, x8, x12, x13, x21, x22,
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * clobbered Flag Groups: FG0, FG1
 */
montmul_mul1:
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

    /* Main loop body of Montgomery Multiplication algorithm */
    /* 1[i]*A */
    jal       x1, mont_loop

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
  jal       x1, cond_sub_to_dmem

  /* restore  dmem pointers for operand A and modulus */
  addi      x16, x6, 0
  addi      x19, x7, 0

  ret
