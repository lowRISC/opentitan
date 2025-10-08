/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

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
  csrrs x17, URND, x0
  sub   x17, x0, x14

  /* z = (X ^ Y) & d. */
  xor x18, x23, x24
  and x18, x17, x18

  /* Sample a random mask r and XOR it to the intermediate result: z = z ^ r. */
  csrrs x17, URND, x0
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
 * Constant-time exponentiation by e-1 = F4-1 = 2^16 = 65536.
 *
 * Calculate C = A^(e-1) mod M in constant. A is assumed to be provided in the
 * Montgomery domain, so is the result C.
 *
 * @param[in]  x16: DMEM pointer to the modulus M
 * @param[in]  x17: DMEM pointer to the base A in the Montgomery domain.
 * @param[out] x18: DMEM pointer to the result C in the Montgomery domain.
 * @param[in]  x30: N, number of limbs per bignum
 * @param[in]   x8: pointer to temp reg, must be set to 4
 * @param[in]   x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[in]   w1: Montgomery Constant m0'
 * @param[in]  w31: all-zero
 *
 * Clobbered registers: x2 to x4, x31, w2
 * Clobbered flag groups: FG0, FG1
 */
modexp_65536:
  /* Compute (N-1). x31 <= x30 - 1 = N - 1 */
  addi      x31, x30, -1

  /* Copy A into the output location. */
  addi      x3, x17, 0
  addi      x4, x18, 0
  loop      x30, 2
    bn.lid    x11, 0(x3++)
    bn.sid    x11, 0(x4++)

  /* Perform 16 squarings to calculate A^(2^16). */
  loopi 16, 9
    addi      x19, x18, 0
    addi      x20, x18, 0
    jal       x1, montmul
    /* Store result at output location in DMEM. */
    addi      x2, x8, 0
    addi      x3, x18, 0
    loop      x30, 2
      bn.sid    x2, 0(x3++)
      addi      x2, x2, 1
    nop

  ret

/**
 * Constant-time, boolean-masked Montgomery ladder bigint exponentiation
 *
 * Calculates: C = modexp(A, d) = A^d mod M
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
 * The input A is blinded for each exponentiation using the inverse-free
 * technique by technique Ebeid and Lambert where
 *
 *   A^d = ((A*R^e)^(d-1))*(A*R^(e-1)) mod M
 *
 * For more information on this blinding strategy, the reader is referred to the
 * paper:
 *
 *   [2] https://dl.acm.org/doi/10.1145/1873548.1873556
 *
 * The computation is carried out in the Montgomery domain, by using the montmul
 * primitive. The squared Montgomery modulus RR and the Montgomery constant m0'
 * have to be precomputed and provided at the appropriate locations in DMEM.
 *
 * This routine operates on the pre-defined memory locations set in
 * `run_rsa_modexp_mem`.
 *
 * @param[in] x29: message blinding flag (enable if non-zero)
 * @param[in] x30: N, number of limbs per bignum
 * @param[in]  w1: Montgomery Constant m0'
 * @param[in] w31: all-zero
 *
 * Clobbered registers: x2 to x22, x31
 *                      w2, w3, w4 to w[4+N-1], w24 to w30
 * Clobbered flag groups: FG0, FG1
 */
modexp:
  # Constant wide register pointers
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  # Compute (N-1): x31 <= x30 - 1 = N - 1
  addi      x31, x30, -1

  # Convert input to Montgomery domain:
  #
  #   [w[4+N-1]:w4] = A' = montmul(A, RR)
  la  x16, rsa_n
  la  x19, r0
  la  x20, RR
  jal x1, montmul

  # Store mont(A) back to DMEM at location r0.
  addi x2, x8, 0
  la   x3, r0
  loop x30, 2
    bn.sid  x2, 0(x3++)
    addi    x2, x2, 1

  # When message blinding is disabled use the work_buf as the location for the
  # pre-computed random indices.
  la x25, work_buf

  beq x0, x29, _message_blinding_prologue_end

  # Sample random blinding factor R of size N limbs and store it in DMEM at r1.
  # Assume it is already in Montgomery form.
  addi x2, x11, 0
  la   x3, r1
  loop x30, 2
    bn.wsrr w2, RND
    bn.sid  x2, 0(x3++)

  # Compute R^(e-1) and store it in DMEM at location r2.
  la x16, rsa_n
  la x17, r1
  la x18, r2
  jal x1, modexp_65536

  # Compute A*R^(e-1) and store it in the work buffer of the scratchpad.
  la x19, r0
  la x20, r2
  jal x1, montmul

  addi x2, x8, 0
  la   x3, work_buf
  loop x30, 2
    bn.sid  x2, 0(x3++)
    addi    x2, x2, 1

  # Compute [w[4+N-1]:w4] = A*R^e.
  la  x19, r1
  la  x20, work_buf
  jal x1, montmul

  # Since d is odd d-1 must be even, hence to have d0 XOR d1 = d-1, the first
  # bit of the share d0 must be flipped.
  la      x16, rsa_d0
  bn.lid  x11, 0(x16)
  bn.addi w30, w31, 1
  bn.xor  w2, w2, w30
  bn.sid  x11, 0(x16)

  # When the message blinding is enable to work_buf is taken by A*R^(e-1), so
  # we need to overwrite the RR which is not needed anymore at this point.
  la x25, RR

_message_blinding_prologue_end:

  # montmul clobbers the flags, clear them here.
  bn.add w31, w31, w31, FG0
  bn.add w31, w31, w31, FG1

  # Step 1 in Algorithm 2 [1]:
  #
  # Initialize r0 and r1 with -M mod R. Note that this Montgomery ladder
  # operates with redundant residuals over Z/RZ as opposed to Z/MZ which
  # significantly simplifies the final comparison step in the Montgomery
  # multiplication. Only the in the very last step of the exponentational, when
  # the output is converted back from the Montgomery form, the value is mapped
  # into Z/NZ (see Section 2.4.2 in https://eprint.iacr.org/2017/1057.pdf for
  # more details on this optimization).
  #
  # [1] asks for r0 and r1 to be initialzed to 1 or montmul(1, RR) in the
  # Montgomery domain over Z/MZ which congruent to -M in Z/RZ.
  la  x2, r0
  la  x3, r1
  la  x5, rsa_n
  loop x30, 4
    bn.lid  x11, 0(x5++)
    bn.subb w2, w31, w2
    bn.sid  x11, 0(x2++)
    bn.sid  x11, 0(x3++)

  # Precomputation of the randomized indices:
  #
  #   `(((b' << R) | (d1 >> 1)) ^ d1) ^ d0`.
  #
  # Store the result in DMEM location RR, as at this point it not needed
  # as all the inputs have been transformed into the Montgomery form.
  #
  # Computes the secret indices (b' ^ bi) ^ ai in Step 5 of Algorithm 2 in [1].
  la x2, rsa_d1
  la x3, rsa_d0
  addi x5, x25, 0

  # Use w24-w26 as intermediate WDRs.
  addi x20, x0, 24
  addi x21, x0, 25
  addi x22, x0, 26

  # Iterate through n-1 limbs (starting from the LSB) and compute
  #   ((d1 >> 1) ^ d1) ^ d0
  loop x31, 9
    bn.lid  x20, 0(x2++)
    bn.lid  x21, 0(x2)
    bn.xor  w31, w31, w31 # dummy instruction
    bn.lid  x22, 0(x3++)
    bn.rshi w25, w25, w24 >> 1
    bn.xor  w24, w24, w25
    bn.xor  w31, w31, w31 # dummy instruction
    bn.xor  w24, w24, w26
    bn.sid  x20, 0(x5++)

  # Generate random bit b'.
  bn.wsrr w25, RND
  bn.add  w26, w25, w25
  csrrs   x4,  FG0, x0
  andi    x4,  x4, 1

  # The last iteration is special, it includes the random bit b' at the MSB.
  bn.rshi w25, w31, w25 >> 255
  bn.lid  x20, 0(x2)
  bn.xor  w31, w31, w31 # dummy instruction
  bn.lid  x22, 0(x3)
  bn.rshi w25, w25, w24 >> 1
  bn.xor  w24, w24, w25
  bn.xor  w31, w31, w31 # dummy instruction
  bn.xor  w24, w24, w26
  bn.sid  x20, 0(x5)

  # Store the converted input back into DMEM r[b' ^ 1] = A'.
  la   x23, r0
  la   x24, r1
  xori x14, x4, 1
  jal  x1, cond_swap_gprs

  addi x2, x8, 0
  loop x30, 2
    bn.sid x2, 0(x19++)
    addi   x2, x2, 1

  # Compute bit length of current bigint size.
  slli  x21, x30, 8

  # Main loop of the exponentiation, iterate over all exponent bits:
  loop x21, 68
    bn.add w31, w31, w31

    # Shift d0 and siphon the shifted out MSB into FG0, x3 = a[i] = d0[i].
    la   x15, rsa_d0
    loop x30, 3
      bn.lid x11, 0(x15)
      # w2 <= w2 << 1
      bn.addc w2, w2, w2
      bn.sid  x11, 0(x15++)
    csrrs x3, FG0, x0
    andi x3, x3, 1
    # Restore the LSB.
    la   x15, rsa_d0
    lw   x22, 0(x15)
    or   x22, x3, x22
    sw   x22, 0(x15)

    # Step 4 in Algorithm 2 [1]:
    #
    # Depending on a[i] assign the input buffers to calculate
    # [w[4+N-1]:w4] = r[a[i]] * r[a[i] ^ 1] and store the result in DMEM[r2].
    la   x23, r0
    la   x24, r1
    addi x14, x3, 0
    jal  x1, cond_swap_gprs

    la x16, rsa_n
    jal x1, montmul

    addi x2, x8, 0
    la   x15, r2
    loop x30, 2
      bn.sid  x2, 0(x15++)
      addi x2, x2, 1

    # Shift secret indices and siphon the shifted out MSB into
    #   x4 = c = (b' ^ bi) ^ ai
    addi   x15, x25, 0
    loop x30, 3
      bn.lid x11, 0(x15)
      # w2 <= w2 << 1
      bn.addc w2, w2, w2
      bn.sid  x11, 0(x15++)
    csrrs x4, FG0, x0
    andi  x4, x4, 1
    # Shift in random bit to properly overwrite the shifted out secret index.
    csrrs x16, URND, x0
    andi  x16, x16, 1
    addi  x15, x25, 0
    lw    x22, 0(x15)
    or    x22, x16, x22
    sw    x22, 0(x15)

    # Step 5 in Algorithm 2 [1]:
    #
    # Calculate [w[4+N-1]:w4] = DMEM[r[c]] * DMEM[r[c]].
    la   x23, r0
    la   x24, r1
    addi x14, x4, 0
    jal x1, cond_swap_gprs

    la   x16, rsa_n
    addi x20, x19, 0
    jal x1, montmul

    # Step 6 in Algorithm 2 [1]:
    #
    # Store r2 and r[c] * r[c] into DMEM such that
    #  DMEM[r[a[i]]]   = r[c] * r[c]
    #  DMEM[r[a[i]^1]] = DMEM[r2]
    la   x23, r0
    la   x24, r1
    addi x14, x3, 0
    jal x1, cond_swap_gprs

    addi x5, x8, 0
    loop x30, 2
      bn.sid x5, 0(x19++)
      addi   x5, x5, 1

    la   x16, r2
    loop x30, 2
      bn.lid x11, 0(x16++)
      bn.sid x11, 0(x20++)

    nop

  # Make sure the output (A*R^e)^(d-1) is in r0.
  la   x23, r0
  la   x24, r1
  la   x14, rsa_d1
  lw   x14, 0(x14)
  andi x14, x14, 1
  jal  x1, cond_swap_gprs

  beq x0, x29, _message_blinding_epilogue_end

  # Unblind ciphertext with A*R^(e-1) such that
  #   DMEM[r0] = A^d mod M = (A*R^e)^(d-1) * A*R^(e-1) mod M
  la x16, rsa_n
  la x20, work_buf
  jal x1, montmul

  addi x2, x8, 0
  la   x3, r0
  loop x30, 2
    bn.sid  x2, 0(x3++)
    addi    x2, x2, 1

  # Convert d0 back such that d0 XOR d1 = d.
  la x12, rsa_d0
  bn.lid x11, 0(x12)
  bn.addi w30, w31, 1
  bn.xor w2, w2, w30
  bn.sid x11, 0(x12)

  la x19, r0

_message_blinding_epilogue_end:

  # Convert back from Montgomery form.
  la  x16, rsa_n
  la  x21, r0
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
 * @param[in]  x17: dptr_RR, dmem pointer to Montgmery constant RR
 * @param[in]  x30: N, number of limbs per bignum
 * @param[in]   w1: m0d', Montgomery constant
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
  addi      x20, x17, 0
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
 * @param[in]  x8: pointer to temp reg, must be set to 4
 * @param[in]  x9: pointer to temp reg, must be set to 3
 * @param[in]  x10: pointer to temp reg, must be set to 4
 * @param[in]  x11: pointer to temp reg, must be set to 2
 * @param[in]   w1: m0d', Montgomery constant
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
