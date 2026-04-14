/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial sampling routines for ML-DSA-87 sign. */

.globl sample_mask_poly

.text

/**
 * Sample an arithmetically shared mask polynomial Y with coefficients in
 * [-GAMMA1+1, GAMMA1] for GAMMA1 = 2^19.
 *
 * This routine is a subprocedure of `ExpandMask` (Algorithm 34) of FIPS-204
 * and is parametrized by a 66-byte secret Boolean-shared seed rho.
 *
 * Note that although rho is a 66-byte value it shall be provided in two
 * 96-byte allocated regions in DMEM for seamless processing by the XOF.
 *
 * @param[in] x2: DMEM address of the first arithmetic share of Y.
 * @param[in] x3: DMEM address of the second arithmetic share of Y.
 * @param[in] x4: DMEM address of the first Boolean share of rho (66 bytes).
 * @param[in] x5: DMEM address of the second Boolean share of rho (66 bytes).
 */
sample_mask_poly:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load GAMMA1 = (2^19, 2^19, ..., 2^19) into w2. */
  bn.not w2, w31
  bn.shv.8s w2, w2 >> 31
  bn.shv.8s w2, w2 << 19

  /* Initialize the SHAKE256 XOF and absorb the 66 bytes of rho. */
  jal x1, xof_shake256_init
  addi x20, x0, 66
  addi x21, x4, 0
  addi x22, x5, 0
  jal x1, xof_absorb
  jal x1, xof_process

  /* Set up WDR pointers. */
  addi x4, x0, 0
  addi x5, x0, 1

  /* In each iteration, we sample 64 coefficients. */
  loopi 4, 44

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
    loopi 8, 22

      /* Sample one shared vector of eight coefficients. */
      loopi 8, 15

        /*
         * Share 0:
         */

        /* Shift in the next 20-bit coefficient and move it to the most
           significant 32-bit slot in w0 and w1. */
        bn.rshi w0, w3, w0 >> 20
        bn.rshi w0, w31, w0 >> 12

        /* Shift out the 20 bits out of the sampled buffer. */
        bn.rshi w3, w4, w3 >> 20
        bn.rshi w4, w5, w4 >> 20
        bn.rshi w5, w6, w5 >> 20
        bn.rshi w6, w7, w6 >> 20
        bn.rshi w7, w31, w7 >> 20

        bn.xor w31, w31, w31 /* dummy */

        /*
         * Share 1:
         */

        bn.rshi w1, w8, w1 >> 20
        bn.rshi w1, w31, w1 >> 12

        bn.rshi w8, w9, w8 >> 20
        bn.rshi w9, w10, w9 >> 20
        bn.rshi w10, w11, w10 >> 20
        bn.rshi w11, w12, w11 >> 20
        bn.rshi w12, w31, w12 >> 20
        /* End of loop */

      /*
       * At this point, w0 and w1 contain eight Boolean-shared coefficients in
       * w0 and w1. We first convert them to arithmetic shares, then calculate
       * w0 = GAMMA1 - w0 mod Q and w1 = 0 - w1 mod Q which implements the
       * `BitUnpack` function (Algorithm 19) of FIPS-204.
       */

      jal x1, sec_b2a_8x32

      /* w0 = GAMMA1 - w0 mod Q. */
      bn.subvm.8S w0, w2, w0
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
  .irp reg, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
