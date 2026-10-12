/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.include "mldsa87.inc"

/* Polynomial sampling routines. */

/* Common */
.globl rej_ntt_poly
.globl sample_in_ball
.globl challenge_hash

/* Keygen */
.globl rej_bounded_poly

/* Sign */
.globl sample_mask_poly

.text

/**
 * Rejection sample a polynomial in the NTT domain.
 *
 * This routine implements the `RejNTTPoly` function (Algorithm 30) of FIPS-204
 * and samples a polynomial directly in the NTT domain with coefficients in the
 * interval [0, Q - 1].
 *
 * @param[in] x2: DMEM output location of sampled polynomial.
 * @param[in] x3: DMEM location of rho (34 bytes), 64 bytes allocated region.
 */
rej_ntt_poly:
  /* Push clobbered registers onto the stack. */
  push x2, x4, x5, x6, x7, x8, x9, x10

  /* (Q - 1)^8 = (0x007fe000, 0x007fe000, ..., 0x007fe000). */
  bn.not w5, w31
  bn.shv.8s w4, w5 >> 22
  bn.shv.8s w4, w4 << 13

  /* (2^23 - 1)^8 = (0x007fffff, 0x007fffff, ..., 0x007fffff). */
  bn.shv.8s w5, w5 >> 9

  /* Initialize the SHAKE128 XOF and absorb the 34 bytes of RHO. */
  jal x1, xof_shake128_init
  addi x20, x0, 34
  addi x21, x3, 0
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /*
   * Part 1: Sample (without rejections) a full 256-coefficient polynomial with
   * coefficients in the interval [0, 2^23 - 1]. The probability that this
   * polynomial does not contain any coefficients that are >= Q is ~78%, hence
   * on average only roughly every 4th polynomial needs to be corrected.
   */

  addi x4, x2, 0

  /* Sample 256 coefficients in the interval [0, 2^23 - 1]. */
  loopi 32, 5
    /* Squeeze 24 bytes from the XOF, enough to populate one 8-coefficient
       WDR. */
    jal x1, xof_squeeze24
    bn.xor w8, w29, w30 /* unmask */

    bn.unpk w0, w31, w8, 0

    /* Set bits 31:23 to 0 to map the 3-byte value to [0, 2^23 - 1]. */
    bn.and w0, w0, w5
    bn.sid x0, 0(x4++)
    /* End of loop */

  /*
   * Part 2: Check and possibly correct the sampled polynomial. Every
   * coefficient x[i] >= Q will be discarded and all the coefficients x[j] for
   * i <= j < 255 will be shifted one position such that x[j] = x[j + 1] and
   * the last coefficient x[255] is squeezed from the XOF.
   */

  /* Index of coefficient to be checked, in reverse order. */
  addi x4, x0, 255 /* counter */

  /* Number of 3-byte squeezes remaining in the buffer. */
  addi x5, x0, 0 /* squeeze */

  /* Q - 1. */
  li x6, 8380416

  /* Iterate over the entire polynomial and check for coefficients that are
     >= Q. 8 coefficients in parallel per iteration. */
  loopi 32, 10
    bn.lid x0, 0(x2)

    /* w0 = 0, if all coefficients are in the interval [0, Q - 1]. */
    bn.sub w0, w4, w0
    bn.shv.8s w0, w0 >> 31

    /* If an invalid coefficient has been detected correct the vector of 8
       coefficients. */
    bn.cmp w0, w31, FG0
    csrrs x7, FG0, x0
    andi x7, x7, 8
    bne x7, x0, _rej_ntt_poly_advance

    jal x1, _rej_ntt_poly_correct

    /* The vector of 8 coefficients has either been valid or been corrected,
       we advance to the next 8 coefficients and adjust the coefficient index. */
_rej_ntt_poly_advance:
    addi x2, x2, 32
    addi x4, x4, -8
    /* End of loop */

  jal x1, xof_finish

  /* Restore clobbered general-purpose registers. */
  pop x10, x9, x8, x7, x6, x5, x4, x2

  ret

/* Correct a vector of 8 coefficients that contains at least one invalid
   value. */
_rej_ntt_poly_correct:
  /* Copy coefficient address and index. */
  addi x7, x2, 0
  addi x8, x4, 0

  /* Iterate over all eight coefficients to find the invalid values and correct
     them. */
  loopi 8, 8
_rej_ntt_poly_correct_loop_start:
    /* Check that that coefficient X[i] < Q and discard it if is not by
       shifting all the following coefficients by one position. */
    lw x9, 0(x7)
    sub x9, x6, x9
    srai x9, x9, 31
    beq x9, x0, _rej_ntt_poly_correct_loop_end

    jal x1, _rej_ntt_poly_shift_right

    /* Having corrected the bad coefficient restart at the top. */
    jal x0, _rej_ntt_poly_correct_loop_start

    /* A coefficient is either valid or has been corrected, advance to the next
       one. */
_rej_ntt_poly_correct_loop_end:
    addi x7, x7, 4
    addi x8, x8, -1
    /* End of loop */

  ret

/* Given an index 0 <= i < 256, shift all the coefficients X[j] one position
   to the right such that X[j] = X[j+1] for i <= j < 255 and set X[255] to
   the output of the XOF. */
_rej_ntt_poly_shift_right:
  /* Copy coefficient address. */
  addi x10, x7, 0

  /* If the coefficient pointer is 0, we have reached the last coefficient
     which is replaced by the XOF output. */
  beq x8, x0, _rej_ntt_poly_shift_right_last_coeff

  /* Shifting loop. Set X[j] = X[j+1] for i <= j < 255. */
  loop x8, 3
    lw x9, 4(x10)
    sw x9, 0(x10)
    addi x10, x10, 4
    /* End of loop */

/* X[255] is set to the output of the XOF. */
_rej_ntt_poly_shift_right_last_coeff:
  /* If the buffer is empty recharge it. */
  bne x5, x0, _rej_ntt_poly_shift_right_recharge_skip

  jal x1, xof_squeeze24
  bn.xor w8, w29, w30 /* unmask */
  addi x5, x0, 8

_rej_ntt_poly_shift_right_recharge_skip:
  /* Pointer to X[248]. */
  addi x10, x10, -28

  bn.lid x0, 0(x10)

  /* Shift in 3 bytes from the XOF. */
  bn.rshi w0, w0, w31 >> 224
  bn.rshi w0, w8, w0 >> 24
  bn.rshi w0, w31, w0 >> 8
  bn.and w0, w0, w5 /* Set bit 23 to 0. */

  bn.sid x0, 0(x10)

  /* Update the XOF buffer and capacity. */
  bn.rshi w8, w31, w8 >> 24
  addi x5, x5, -1

  ret

/**
 * Sample a challenge polynomial C with coefficients in {-1, 0, 1} and Hamming
 * weight TAU = 60.
 *
 * This routine implements the `SampleInBall` function (Algorithm 29) in
 * FIPS-204 and is an adapted variant of the "inside-out" Fisher-Yates shuffle:
 * https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
 *
 * @param[in] x2: Output location of the sampled polynomial C.
 * @param[in] x3: DMEM location of rho (64 bytes).
 */
sample_in_ball:
  /* Push clobbered registers onto the stack. */
  push x5, x6, x7, x8, x9, x10, x11, x12

  /* Scratch DMEM location to transfer a value in a WDR to a GPR. */
  la x4, mldsa87_sample_in_ball_scratch

  /* Make sure the target location of the sampled polynomial is set to 0. */
  addi x20, x2, 0
  addi x21, x0, 32
  jal x1, zeroize

  /* Loop counter: i = 256-TAU = 256-60 = 196. */
  addi x6, x0, 196

  /* Initialize the SHAKE256 XOF and absorb the 64 bytes of rho. */
  jal x1, xof_shake256_init
  addi x20, x0, 64
  addi x21, x3, 0
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /*
   * Squeeze 8 bytes to create the 64-bit string indicator string h.
   */

  addi x20, x0, 8
  jal x1, xof_squeeze32
  bn.xor w29, w29, w30

  /* Isolate the 64 least significant bits. */
  bn.rshi w2, w29, w31 >> 64
  bn.rshi w2, w31, w2 >> 192

  /* Use the remaining 192 bits for the rejection loop sampling. */
  bn.rshi w29, w31, w29 >> 64
  addi x10, x0, 24 /* Number of bytes remaining in the buffer. */

  /* Byte mask. */
  bn.addi w1, w31, 0xff

  /* Set up constants. */
  li x11, 1
  li x12, 8380417 /* Q */

  /*
   * In the following, we denote by C[i] the i-th coefficient of the sampled
   * polynomial. At the beginning of the main loop we have C[i] = 0, for
   * 0 <= i < 256.
   */

  /* Set TAU = 60 random coefficients of C to either 1 or -1 depending on the
   * indicator string h. */
  loopi 60, 28
_sample_in_ball_coeff:
    /* Squeeze a new batch of 32 bytes, if the buffer has been depleted. */
    bne x10, x0, _sample_in_ball_skip_squeeze

    jal x1, xof_squeeze32
    bn.xor w29, w29, w30

    addi x10, x0, 32

_sample_in_ball_skip_squeeze:
    /* Isolate the least signficant byte and store it in DMEM so that the value
       can be transfered to a GPR. */
    bn.and w0, w29, w1
    bn.sid x0, 0(x4)

    /* Update the buffer and a capacity counter. */
    bn.rshi w29, w31, w29 >> 8
    addi x10, x10, -1

    /* Perform the comparison j > i:
       If j > i, then the MSB of i - j will be set. */
    lw   x7, 0(x4)
    sub  x8, x6,  x7
    srli x8, x8,  31
    bne  x8, x0, _sample_in_ball_coeff

    /* Derive the DMEM addresses of the coefficients C[i] and C[j]. */
    slli x8, x7,  2
    add  x8, x8, x2
    slli x7, x6,  2
    add  x7, x7, x2

    /* C[i] = C[j]. */
    lw x9, 0(x8)
    sw x9, 0(x7)

    /* Depending on the LSB of h we select either 1 or -1 mod q and store it at
       C[j]. */
    bn.sub  w2,  w2, w31
    csrrs   x7, FG0,  x0
    andi    x7,  x7, 0x4

    /* x7 = 1, if h[i + TAU - 256] = 0, else x7 = -1 mod Q. */
    srli x7, x7, 2
    sub x7, x0, x7
    and x7, x7, x12
    xor x7, x7, x11

    sw x7, 0(x8)

    /* Update i and h. */
    addi x6, x6, 1
    bn.rshi w2, w31, w2 >> 1
    /* End of loop */

  jal x1, xof_finish

  /* Restore clobbered general-purpose registers. */
  pop x12, x11, x10, x9, x8, x7, x6, x5

  ret

/**
 * Calculate the challenge hash c = SHAKE256(mu|w1_enc).
 *
 * @param[in] x2: DMEM address of mu (64 bytes).
 * @param[in] x3: DMEM address of the w1_enc vector (1024 bytes).
 * @param[in] x4: DMEM address of the output challenge hash c.
 */
challenge_hash:
  /* This routine is only called from the top-level, so no need to preserve
     the clobbered registers. */

  jal x1, xof_shake256_init

  /* Absorb the 64 bytes of mu. */
  addi x20, x0, 64
  addi x21, x2, 0
  addi x22, x0, 0
  jal x1, xof_absorb

  /* Absorb the 1024 bytes of w1_enc vector. */
  addi x20, x0, 1024
  addi x21, x3, 0
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Squeeze the 64-byte challenge hash c. */
  jal x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x4++)
  jal x1, xof_squeeze32
  bn.xor w0, w29, w30
  bn.sid x0, 0(x4++)

  jal x1, xof_finish

  ret

.data
.balign 32

/* Scratch buffer of `sample_in_ball` (declared in `mldsa87_mem.s`). */
mldsa87_sample_in_ball_scratch:
.zero 32

/* Polynomial sampling routines for ML-DSA-87 keygen. */

.text

/**
 * Rejection sample a polynomial with coefficients in the interval [-ETA, ETA].
 *
 * This routine can be used to sample a secret-key polynomial S as part of the
 * vectors S1 and S2 whose coefficients are uniformly distributed in the
 * interval [-ETA, ETA] for ETA = 2. This is a direct implementation of the
 * `RejBoundedPoly` function (Algorithm 31) of FIPS-204.
 *
 * Note that although the seed rho is a 66-byte Boolean-shared value it shall
 * be provided in two 96-byte allocated regions in DMEM for seamless
 * processing by the XOF.
 *
 * @param[in] x2: DMEM address of the first Boolean share of rho.
 * @param[in] x3: DMEM address of the second Boolean share of rho.
 * @param[in] x4: DMEM address of the first arithmetic share of the sampled S.
 * @param[in] x5: DMEM address of the second arithmetic share of the sampled S.
 */
rej_bounded_poly:
  /* Push clobbered general-purpose registers onto the stack. */
  push x4, x5, x6, x7, x8, x9

  /* Load [ETA, ETA, ..., ETA] into w16. */
  bn.not w16, w31
  bn.shv.8s w16, w16 >> 31
  bn.shv.8s w16, w16 << 1

  /* Set the rejection bound to 14. */
  bn.addi w17, w31, 14

  /* Prepare a 32-bit mask. w12 = 0x000...000ffffffff. */
  bn.not w12, w31
  bn.rshi w12, w31, w12 >> 224

  /* Prepare a 4-bit mask. w13 = 0xfff...fff0000000f. */
  bn.not w13, w31
  bn.rshi w13, w13, w31 >> 224
  bn.addi w13, w13, 15

  /* Initialize the SHAKE256 XOF and absorb the 66 bytes of rho. */
  jal x1, xof_shake256_init
  addi x20, x0, 66
  addi x21, x2, 0
  addi x22, x3, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Number of half-byte words left in the buffer. */
  addi x6, x0, 0

  /* WDR pointers. */
  addi x7, x0, 0
  addi x8, x0, 1

  /* Initialize the WDRs that hold intermediate results with randomness. */
  bn.wsrr w4, URND
  bn.wsrr w5, URND
  bn.wsrr w10, URND
  bn.wsrr w11, URND

  /*
   * The following loop unfolds in two parts. First, rejection sample a
   * Boolean shared vector x consisting of 8 4-bit coefficients in the interval
   * [0, 14]. Second, compute x mod 5 and convert the coefficients to
   * arithmetic shares. Repeat this 32 times until all the coefficients of the
   * polynomial have been sampled.
   */
  loopi 32, 38
    loopi 8, 27
     /* If the squeezed buffer is empty re-squeeze a new batch of 64 4-bit
        coefficients. */
_rej_bounded_poly_squeeze_start:
      bne x6, x0, _rej_bounded_poly_squeeze_end

      /* Squeeze and reset the counter. */
      jal x1, xof_squeeze32
      addi x6, x0, 64

      /* Rejection loop. Check if a 4-bit value is in interval [0, 14], if so
         keep it otherwise try the next 4-bit value. */
_rej_bounded_poly_squeeze_end:
      /* Update the buffer capacity. */
      addi x6, x6, -1

      /* Extract a Boolean-shared 4-bit value x[i] from the XOF buffers
         (w29, w30) and place it at the LSB in w0 and w1. */

      /* Randomness to shift into registers when a coefficient is extracted.
         This avoids that few secrets bits are isolated in an all-zero WDR. */
      bn.wsrr w6, URND
      bn.wsrr w7, URND

      /*
       * Share 0:
       */

      /* Extract 4 bits from the buffer and place at the LSB of w4. */
      bn.rshi w4, w29, w4 >> 4
      bn.rshi w4, w6, w4 >> 252

      /* Mask out the lower 4 bits. This is necessary for the correctness of
         the `sec_leq_8x32` bound check below. */
      bn.and w4, w4, w13

      /* Remove the extracted 4 bits from the buffer. */
      bn.rshi w29, w6, w29 >> 4

      bn.xor w31, w31, w31 /* dummy */

      /*
       * Share 1:
       */

      /* Extract 4 bits from the buffer and place at the LSB of w5. */
      bn.rshi w5, w30, w5 >> 4
      bn.rshi w5, w7, w5 >> 252

      /* Mask out the lower 4 bits. This is necessary for the correctness of
         the `sec_leq_8x32` bound check below. */
      bn.and w5, w5, w13

      /* Remove the extracted 4 bits from the buffer. */
      bn.rshi w30, w7, w30 >> 4

      /* Check that x[i] <= 14. */
      bn.mov w0, w4
      bn.mov w2, w17 /* splice */
      bn.mov w1, w5
      jal x1, sec_leq_8x32

      /* We are only interested in the lower 32 bits of the `sec_leq_8x32`
         result, mask them out here. */
      bn.and w0, w0, w12

      /* If x[i] > 14, then x9 = 1, else x9 = 0. */
      bn.cmp w0, w31, FG0
      csrrs x9, FG0, x0
      andi x9, x9, 0x8
      bne x9, x0, _rej_bounded_poly_squeeze_start

      /* x[i] has passed the rejection check and can be shifted into w10 and
         w11. */
      bn.rshi w10, w4, w10 >> 32
      bn.xor w31, w31, w31 /* dummy */
      bn.rshi w11, w5, w11 >> 32
      /* End of loop */

    /*
     * At this point, we have a Boolean-shared vector x with 8 uniformly
     * distributed coefficients in the interval [0, 14]. First calculate
     * x = x mod 5, then convert them to arithmetic shares and calculate
     * x = 2 - x mod Q. This part is an implementation of the
     * `CoeffFromHalfByte` function (Algorithm 15) of FIPS-204.
     */

    /* Compute x mod 5 and convert to arithmetic shares. */
    bn.mov w0, w10
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w1, w11

    jal x1, sec_mod5_8x32
    jal x1, sec_b2a_8x32

    /* Compute 2 - x mod Q and store the vector in the output DMEM location. */
    bn.subvm.8S w0, w16, w0
    bn.sid x7, 0(x4++)

    bn.xor w31, w31, w31 /* dummy */

    bn.subvm.8S w1, w31, w1
    bn.sid x8, 0(x5++)
    /* End of loop */

  jal x1, xof_finish

  /* Restore clobbered general-purpose registers. */
  pop x9, x8, x7, x6, x5, x4

  ret

/* Polynomial sampling routines for ML-DSA-87 sign. */

.text

/**
 * Sample an arithmetically shared mask polynomial Y with coefficients in
 * [-GAMMA1+1, GAMMA1] for GAMMA1 = 2^19.
 *
 * This routine is a subprocedure of `ExpandMask` (Algorithm 34) of FIPS-204
 * and is parametrized by a 64-byte secret Boolean-shared seed rho and a 2-byte
 * nonce kappa (provided in 32-byte DMEM region).
 *
 * @param[in] x2: DMEM address of the first arithmetic share of Y.
 * @param[in] x3: DMEM address of the second arithmetic share of Y.
 * @param[in] x4: DMEM address of the first Boolean share of rho (64 bytes).
 * @param[in] x5: DMEM address of the second Boolean share of rho (64 bytes).
 * @param[in] x6: DMEM address of KAPPA (2 bytes, 32-byte DMEM region).
 */
sample_mask_poly:
  /* Push clobbered registers onto the stack. */
  push x2, x3, x4, x5

  /* Load GAMMA1 = (2^19, 2^19, ..., 2^19) into w15. */
  bn.not w15, w31
  bn.shv.8s w15, w15 >> 31
  bn.shv.8s w15, w15 << 19

  /* Prepare 20-bit masks. w16 = (0x000fffff, ..., 0x000fffff). */
  bn.not w16, w31
  bn.shv.8s w16, w16 >> 12

  /* Initialize the SHAKE256 XOF and absorb the 64 bytes of rho. */
  jal x1, xof_shake256_init
  addi x20, x0, 64
  addi x21, x4, 0
  addi x22, x5, 0
  jal x1, xof_absorb

  /* Absorb the 2-byte nonce kappa. */
  addi x20, x0, 2
  addi x21, x6, 0
  addi x22, x0, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Set up WDR pointers. */
  addi x4, x0, 0
  addi x5, x0, 1

  /* Initialize the registers that hold the compressed polynomial shares with
     randomness. This avoids isolating secrets bits in an all-zero register
     during the shifting operations. */

  /* Share 0. */
  bn.wsrr w0, URND
  bn.wsrr w3, URND
  bn.wsrr w4, URND
  bn.wsrr w5, URND
  bn.wsrr w6, URND
  bn.wsrr w7, URND

  /* Share 1. */
  bn.wsrr w1, URND
  bn.wsrr w8, URND
  bn.wsrr w9, URND
  bn.wsrr w10, URND
  bn.wsrr w11, URND
  bn.wsrr w12, URND

  /* In each iteration, we sample 64 coefficients. */
  loopi 4, 49

    /*
     * Each coefficient of the mask polynomial has a size of 20 bits. Since
     * LCM(20, 256) = 1280 = 5 * 256, we can fully fill five WDRs w3-w7 (share
     * 0) and w8-w12 (share 1) with sampled bits which in turn is exactly the
     * amount of bits we need to create 64 coefficients.
     */

    jal x1, xof_squeeze32
    bn.mov w3, w29
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w8, w30

    jal x1, xof_squeeze32
    bn.mov w4, w29
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w9, w30

    jal x1, xof_squeeze32
    bn.mov w5, w29
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w10, w30

    jal x1, xof_squeeze32
    bn.mov w6, w29
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w11, w30

    jal x1, xof_squeeze32
    bn.mov w7, w29
    bn.xor w31, w31, w31 /* dummy */
    bn.mov w12, w30

    /* Sample 64 coefficients in steps of eight at at time. */
    loopi 8, 27

      /* Sample one shared vector of eight coefficients. */
      loopi 8, 17

        /* Randomness to shift into registers when a coefficient is extracted.
           This avoids that few secrets bits are isolated in an all-zero WDR. */
        bn.wsrr w13, URND
        bn.wsrr w14, URND

        /*
         * Share 0:
         */

        /* Shift in the next 20-bit coefficient and move it to the most
           significant 32-bit slot in w0 and w1. */
        bn.rshi w0, w3, w0 >> 20
        bn.rshi w0, w13, w0 >> 12

        /* Shift out the 20 bits out of the sampled buffer. */
        bn.rshi w3, w4, w3 >> 20
        bn.rshi w4, w5, w4 >> 20
        bn.rshi w5, w6, w5 >> 20
        bn.rshi w6, w7, w6 >> 20
        bn.rshi w7, w13, w7 >> 20

        bn.xor w31, w31, w31 /* dummy */

        /*
         * Share 1:
         */

        bn.rshi w1, w8, w1 >> 20
        bn.rshi w1, w14, w1 >> 12

        bn.rshi w8, w9, w8 >> 20
        bn.rshi w9, w10, w9 >> 20
        bn.rshi w10, w11, w10 >> 20
        bn.rshi w11, w12, w11 >> 20
        bn.rshi w12, w14, w12 >> 20
        /* End of loop */

      /*
       * At this point, w0 and w1 contain eight Boolean-shared coefficients in
       * w0 and w1. We first convert them to arithmetic shares, then calculate
       * w0 = GAMMA1 - w0 mod Q and w1 = 0 - w1 mod Q which implements the
       * `BitUnpack` function (Algorithm 19) of FIPS-204.
       */

      /* Mask out the lower 20 bits of each 32-bit chunk. */
      bn.and w0, w0, w16
      bn.xor w31, w31, w31 /* dummy */
      bn.and w1, w1, w16

      jal x1, sec_b2a_8x32

      /* w0 = GAMMA1 - w0 mod Q. */
      bn.subvm.8S w0, w15, w0
      bn.sid x4, 0(x2++)

      bn.xor w31, w31, w31 /* dummy */

      /* w1 = 0 - w1 mod Q. */
      bn.subvm.8S w1, w31, w1
      bn.sid x5, 0(x3++)
      /* End of loop */

    nop
    /* End of loop */

  jal x1, xof_finish

  /* Restore clobbered general-purpose registers. */
  pop x5, x4, x3, x2

  ret
