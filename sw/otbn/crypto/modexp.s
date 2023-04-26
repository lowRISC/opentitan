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
sel_sqr_or_sqrmul:
  /* iterate over all limbs */
  loop      x30, 4
    /* load limb from dmem */
    bn.lid    x9, 0(x21)

    /* load limb from regfile buffer */
    bn.movr   x11, x8++

    /* conditional select: w0 = FG0.C?w[x8+i]:dmem[x21+i] */
    bn.sel    w0, w2, w3, C

    /* store selected limb to dmem */
    bn.sid    x0, 0(x21++)

  ret


/**
 * Constant-time bigint modular exponentiation
 *
 * Returns: C = modexp(A,E) = A^E mod M
 *
 * This implements the square and multiply algorithm, i.e. for each bit of the
 * exponent both the squared only and the squared with multiply results are
 * computed but one result is discarded.
 * Computation is carried out in the Montgomery domain, by using the montmul
 * primitive.
 * The squared Montgomery modulus RR and the Montgomery constant m0' have to
 * be precomputed and provided at the appropriate locations in dmem.
 *
 * Flags: The states of both FG0 and FG1 depend on intermediate values and are
 *        not usable after return.
 *
 * The base bignum A is expected in the input buffer, the exponent E in the
 * exp buffer, the result C is written to the output buffer.
 * Note, that the content of both, the input buffer and the exp buffer is
 * modified during execution.
 *
 * @param[in]   x2: dptr_c, dmem pointer to buffer for output C
 * @param[in]  x14: dptr_a, dmem pointer to first limb of input A
 * @param[in]  x15: dptr_e, dmem pointer to first limb of exponent E
 * @param[in]  x16: dptr_M, dmem pointer to first limb of modulus M
 * @param[in]  x17: dptr_m0d, dmem pointer to first limb of m0'
 * @param[in]  x18: dptr_RR, dmem pointer to first limb of RR
 * @param[in]  x30: N, number of limbs per bignum
 * @param[in]  w31: all-zero
 * @param[out] dmem[dptr_c:dptr_c+N*32] C, A^E mod M
 *
 * clobbered registers: x3 to x13, x16 to x31
 *                      w0 to w3, w24 to w30
 *                      w4 to w[4+N-1]
 * clobbered Flag Groups: FG0, FG1
 */
modexp:
  /* prepare pointers to temp regs */
  li         x8, 4
  li         x9, 3
  li        x10, 4
  li        x11, 2

  /* Compute (N-1).
       x31 <= x30 - 1 = N - 1 */
  addi      x31, x30, -1

  /* Convert input to montgomery domain.
       dmem[dptr_a] <= montmul(A,RR) = A*R mod M */
  addi      x19, x14, 0
  addi      x20, x18, 0
  addi      x21, x14, 0
  jal       x1, montmul
  loop      x30, 2
    bn.sid    x8, 0(x21++)
    addi      x8, x8, 1

  /* zeroize w2 and reset flags */
  bn.sub    w2, w2, w2

  /* initialize the output buffer with -M */
  addi      x3, x16, 0
  addi      x21, x2, 0
  loop      x30, 3
    /* load limb from modulus */
    bn.lid    x11, 0(x3++)

    /* subtract limb from 0 */
    bn.subb   w2, w31, w2

    /* store limb in dmem */
    bn.sid    x11, 0(x21++)

  /* compute bit length of current bigint size */
  slli      x24, x30, 8

  /* iterate over all bits of bigint */
  loop      x24, 20
    /* square: out = montmul(out,out)  */
    addi      x19, x2, 0
    addi      x20, x2, 0
    addi      x21, x2, 0
    jal       x1, montmul
    /* Store result in dmem starting at dmem[dptr_c] */
    loop      x30, 2
      bn.sid    x8, 0(x21++)
      addi      x8, x8, 1

    /* multiply: out = montmul(in,out) */
    addi      x19, x14, 0
    addi      x20, x2, 0
    addi      x21, x2, 0
    jal       x1, montmul

    /* w2 <= w2 << 1 */
    bn.add    w2, w2, w2

    /* the loop performs a 1-bit left shift of the exponent. Last MSB moves
       to FG0.C, such that it can be used for selection */
    addi      x20, x15, 0
    loop      x30, 3
      bn.lid    x11, 0(x20)
      /* w2 <= w2 << 1 */
      bn.addc   w2, w2, w2
      bn.sid    x11, 0(x20++)

    /* select squared or squared+multiplied result */
    addi      x21, x2, 0
    jal       x1, sel_sqr_or_sqrmul

    nop

  /* convert back from montgomery domain */
  /* out = montmul(out,1) = out/R mod M  */
  addi      x19, x2, 0
  addi      x21, x2, 0
  jal       x1, montmul_mul1

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
 * @param[in]  x17: dptr_m0d, dmem pointer to Mongtgomery constant m0'
 * @param[in]  x18: dptr_RR, dmem pointer to Montgmery constant RR
 * @param[in]  x30: N, number of limbs per bignum
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
