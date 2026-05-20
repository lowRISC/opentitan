/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial decoding routines. */

.globl decode_s

.text

/**
 * Decode an encoded Boolean-shared secret key S{1,2} polynomial to the
 * arithmetically shared canonical representation.
 *
 * An encoded Boolean-shared S{1,2} polynomial consists of 256 3-bit (768 bit
 * per share) coefficients in the interval [-ETA, ETA]. This routine implements
 * the `BitUnpack` function (Algorithm 19) as part of `skDecode` (Algorithm 25)
 * in FIPS-204.
 *
 * @param[in] x2: DMEM pointer to first Boolean share of the encoded S.
 * @param[in] x3: DMEM pointer to second Boolean share of the encoded S.
 * @param[in] x4: DMEM pointer to first arithmetic share of the decoded S.
 * @param[in] x5: DMEM pointer to second arithmetic share of the decoded S.
 */
decode_s:
  /* Push clobbered registers onto the stack. */
  .irp reg, x4, x5, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Prepare subtraction vector ETA = 2: w2 = [2, 2, 2, 2, 2, 2, 2, 2]. */
  bn.not w2, w31
  bn.shv.8s w2, w2 >> 31
  bn.shv.8s w2, w2 << 1

  /* An encoded S{1,2} polynomial is 256 * 3 = 768 bits or three 256-bit words.
     Load both Boolean shares here into w3-w5 and w6-w8. */
  li x6, 3
  bn.lid x6++, 0(x2)
  bn.lid x6++, 32(x2)
  bn.lid x6++, 64(x2)

  li x6, 6
  bn.lid x6++, 0(x3)
  bn.lid x6++, 32(x3)
  bn.lid x6++, 64(x3)

  /*
   * Decode the Boolean-shared polynomial in steps of 64 3-bit coefficients
   * that are converted to arithmetic shares and stored in DMEM as 64 32-bit
   * arithmetically shared coefficients in the canonical representation. In
   * each step, 192 bits from the encoded S{1,2} are extracted and processed
   * per share.
   */

  /* Bit unpack to the first 192 bits. */
  bn.mov w9, w3
  bn.xor w31, w31, w31 /* dummy */
  bn.mov w10, w6
  jal x1, _bit_unpack_s

  /* 64 bits left in w3/w6. */
  bn.rshi w9, w4, w3 >> 192
  bn.xor w31, w31, w31 /* dummy */
  bn.rshi w10, w7, w6 >> 192
  jal x1, _bit_unpack_s

  /* 128 bits left in w4/w7. */
  bn.rshi w9, w5, w4 >> 128
  bn.xor w31, w31, w31 /* dummy */
  bn.rshi w10, w8, w7 >> 128
  jal x1, _bit_unpack_s

  /* 192 bits left in w5/w8. */
  bn.rshi w9, w31, w5 >> 64
  bn.xor w31, w31, w31 /* dummy */
  bn.rshi w10, w31, w8 >> 64
  jal x1, _bit_unpack_s

  /* Restore clobbered general-purpose registers. */
  .irp reg, x7, x6, x5, x4
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Bit-unpack 192 Boolean-shared bits in w9 and w10 to the interval
 * [-ETA, ETA] converted to arithmetic shares.
 */
_bit_unpack_s:
  /* WDR pointers */
  li x6, 0
  li x7, 1

  /* Prepare 3-bit masks. w13 = (0x00000007, ..., 0x00000007). */
  bn.not w13, w31
  bn.shv.8s w13, w13 >> 29

  /* In each iteration, we decode 8 Boolean-shared coefficients that are
     bit-unpacked and converted to arithmetic shares in w0 and w1. */
  loopi 8, 21

    /* Initialize the WDRs that hold intermediate results with randomness. */
    bn.wsrr w0, URND
    bn.wsrr w1, URND

    loopi 8, 9

      /* Randomness to shift into registers when a coefficient is extracted.
         This avoids that few secrets bits are isolated in an all-zero WDR. */
      bn.wsrr w11, URND
      bn.wsrr w12, URND

      /* Share 0: */

      /* Shift in a 3-bit chunk into w0. */
      bn.rshi w0, w9, w0 >> 3
      bn.rshi w0, w11, w0 >> 29
      /* Remove the processed 3-bit chunk from w9. */
      bn.rshi w9, w11, w9 >> 3

      /* Share 1: */

      bn.xor w31, w31, w31 /* dummy */

      /* Shift in a 3-bit chunk into w1. */
      bn.rshi w1, w10, w1 >> 3
      bn.rshi w1, w12, w1 >> 29
      /* Remove the processed 3-bit chunk from w10. */
      bn.rshi w10, w12, w10 >> 3
      /* End of loop */

    /* Finalize the bit unpacking by converting the 8 coefficients to
       arithmetic shares and computing the subtraction ETA - x mod Q. */

    /* Mask out the lower 3 bits of each 32-bit chunk. */
    bn.and w0, w0, w13
    bn.xor w31, w31, w31 /* dummy */
    bn.and w1, w1, w13

    /* Convert the Boolean shares in w0 and w1 to arithmetic shares. */
    jal x1, sec_b2a_8x32

    /* Share 0: */

    /* ETA - x mod Q. */
    bn.subvm.8S w0, w2, w0
    bn.sid x6, 0(x4++)

    /* Share 1: */

    bn.xor w31, w31, w31 /* dummy */

    /* 0 - x mod Q. */
    bn.subvm.8S w1, w31, w1
    bn.sid x7, 0(x5++)
    /* End of loop */

  ret
