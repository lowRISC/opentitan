/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines for ML-DSA-87 sign. */

.globl decode_t0
.globl decode_w1
.globl encode_z
.globl decode_s

.text

/**
 * Decode a T0 polynomial to the canonical representation.
 *
 * An encoded T0 polynomial consists of 256 13-bit (3328 bits in total)
 * coefficients in the interval ]-2^(D-1), 2^(D-1)] for D = 13.
 *
 * This routine implements the `BitUnpack` function (Algorithm 19) as part of
 * `skDecode` (Algorithm 25) in FIPS-204.
 *
 * @param[in] x2: DMEM pointer to the encoded polynomial T0 (416 bytes).
 * @param[in] x3: DMEM pointer to the decoded polynomial T0 (1024 bytes).
 */
decode_t0:
  /* Push clobbered registers onto the stack. */
  .irp reg, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Prepare subtraction vector 2^(D-1) = 2^(13-1) = 4096:
     [4096, 4096, 4096, 4096, 4096, 4096, 4096, 4096]. */
  bn.not w4, w31
  bn.shv.8s w4, w4 >> 31
  bn.shv.8s w4, w4 << 12

  /* An undecoded T0 polynomial is 256 * 13 = 3328 bits or 13 256-bit words.
     Load them here into w5-w17. */
  addi x4, x0, 5
  addi x5, x2, 0
  loopi 13, 2
    bn.lid x4, 0(x5++)
    addi   x4, x4, 1
    /* End of loop */

  /*
   * Decode the polynomial in steps of 32 32-bit coefficients that are then
   * stored at DMEM[x3]. In each step, 32 * 13 = 416 bits from the undecoded T0
   * are extracted and processed.
   */

  /* Bit unpack the first 416 bits (32 coefficients). */
  bn.mov w18, w5
  bn.mov w19, w6
  jal x1, _bit_unpack_t0

  /* 96 bits left in w6. */
  bn.rshi w18, w7, w6 >> 160
  bn.rshi w19, w8, w7 >> 160
  jal x1, _bit_unpack_t0

  /* 192 bits left in w8. */
  bn.rshi w18,  w9, w8 >> 64
  bn.rshi w19, w10, w9 >> 64
  jal x1, _bit_unpack_t0

  /* 32 bits left in w9. */
  bn.rshi w18, w10,  w9 >> 224
  bn.rshi w19, w11, w10 >> 224
  jal x1, _bit_unpack_t0

  /* 128 bits left in w11. */
  bn.rshi w18, w12, w11 >> 128
  bn.rshi w19, w13, w12 >> 128
  jal x1, _bit_unpack_t0

  /* 224 bits left in w13. */
  bn.rshi w18, w14, w13 >> 32
  bn.rshi w19, w15, w14 >> 32
  jal x1, _bit_unpack_t0

  /* 64 bits left in w14. */
  bn.rshi w18, w15, w14 >> 192
  bn.rshi w19, w16, w15 >> 192
  jal x1, _bit_unpack_t0

  /* 160 bits left in w16. */
  bn.rshi w18, w17, w16 >> 96
  bn.rshi w19, w31, w17 >> 96
  jal x1, _bit_unpack_t0

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Extract 416 bits (32 13-bit coefficients) from w18 and w19 and expand them
 * into 32 32-bit coefficients in the range ]4096,4096] before storing them
 * in DMEM.
 */
_bit_unpack_t0:
  /* Setup WDR output pointer and temp pointer. */
  li x5, 0
  li x6, 20

  /* Extract 32 13-bit chunks into 4 WDRs (w0-w3) containing 8 32-bit
     coefficients each. */
  loopi 4, 7
    loopi 8, 4
      /* Shift in a 13-bit chunk into the most significant 32-bit coefficient. */
      bn.rshi w20, w18, w20 >> 13
      bn.rshi w20, w31, w20 >> 19
      /* Remove the unpacked 13-bit chunk from w18, w19. */
      bn.rshi w18, w19, w18 >> 13
      bn.rshi w19, w31, w19 >> 13
      /* End of loop */

    /* Compute 4096 - x mod Q for eight 32-bit coefficients. */
    bn.subvm.8S w20, w4, w20
    bn.movr x5++, x6
    /* End of loop */

  /* w0-w3 contain the 32 32-bit centered coefficients. */
  addi x20, x0, 0
  bn.sid x20++, 0(x3)
  bn.sid x20++, 32(x3)
  bn.sid x20++, 64(x3)
  bn.sid x20++, 96(x3)
  addi x3, x3, 128

  ret

/**
 * Decode a W1 polynomial to the canonical representation.
 *
 * The W1 polynomials are the high bits (after decomposition) of the commitment
 * polynomials W. Each coefficient of W1 is 4 bits, hence an encoded polynomial
 * consists of 4 * 256 = 1024 bits or 128 bytes.
 *
 * This routine is not part of the FIPS-204 specification but it helps us
 * reduce the DMEM footprint by keeping the W1 polynomials in encoded form
 * throughout the sign procedure. It is the inverse of the `w1Encode` function
 * (Algorithm 28) in FIPS-204.
 *
 * @param[in] x2: DMEM location of the encoded W1 polynomial.
 * @param[in] x3: DMEM location of the decoded W1 polynomial.
 */
decode_w1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* WDR pointer. */
  addi x4, x0, 8

  /* The encoded polynomial W1 fits into 4 WDRs containing 64 coefficients each,
     thus decode it in 4 iterations. */
  loopi 4, 3
    bn.lid x4, 0(x2++)
    jal x1, _simple_bit_unpack_w1
    nop
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Decode 64 4-bit coefficients in a single WDR w8. This subroutine is akin to
 * the `SimpleBitUnpack` function (Algorithm 18) of FIPS-204.
 */
_simple_bit_unpack_w1:
  /* WDR pointers for intermediate results. */
  addi x5, x0, 0
  addi x6, x0, 9

  /* Decode 64 4-bit to 64 32-bit coefficients in w0-w7. */
  loopi 8, 5
    loopi 8, 3
      /* Shift out the least significant bits into a 32-bit slot in w9. */
      bn.rshi w9, w8, w9 >> 4
      bn.rshi w9, w31, w9 >> 28
      bn.rshi w8, w31, w8 >> 4
      /* End of loop */
    bn.movr x5++, x6
    /* End of loop */

  /* Store the decoded 64 32-bit coefficients into DMEM. */
  addi x7, x0, 0
  bn.sid x7++, 0(x3)
  bn.sid x7++, 32(x3)
  bn.sid x7++, 64(x3)
  bn.sid x7++, 96(x3)
  bn.sid x7++, 128(x3)
  bn.sid x7++, 160(x3)
  bn.sid x7++, 192(x3)
  bn.sid x7++, 224(x3)
  addi x3, x3, 256

  ret

/**
 * Encode a Z polynomial into a dense representation.
 *
 * A Z polynomial consists of 256 20-bit coefficients in the range
 * ]-GAMMA1, GAMMA1] for GAMMA1 = 2^19 hence its encoded representation has a
 * size of 256 * 20 = 5120 bits of 640 bytes. This routine is a part of the
 * `sigEncode` function (Algorithm 26) of FIPS-204.
 *
 * @param[in] x2: DMEM location of the decoded Z polynomial.
 * @param[in] x3: DMEM location of the encoded Z polynomial.
 */
encode_z:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* w5 = 2^GAMMA1 = 2^19. */
  bn.not w5, w31
  bn.shv.8s w5, w5 >> 31
  bn.shv.8s w5, w5 << 19

  /* Since LCM(20, 256) = 1280 = 5 * 256, we can store densely encoded 64
     coefficients in 5 WDRs. Hence in each iteration, we load 64 coefficients
     into w6-w13 before bit packing them.*/
  loopi 4, 11
    addi x4, x0, 6
    bn.lid x4++, 0(x2)
    bn.lid x4++, 32(x2)
    bn.lid x4++, 64(x2)
    bn.lid x4++, 96(x2)
    bn.lid x4++, 128(x2)
    bn.lid x4++, 160(x2)
    bn.lid x4++, 192(x2)
    bn.lid x4++, 224(x2)

    jal x1, _bit_pack_z

    addi x2, x2, 256
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Bit pack 64 coefficients in w6-w13 into a dense representation before
 * storing them into DMEM. This routine is akin to the `BitPack` function
 * (Algorithm 17) of FIPS-204.
 */
_bit_pack_z:
  /* In each iteration densely pack 8 coefficients into w0-w4. */
  loopi 8, 16

    /* Calculate GAMMA1 - x mod Q to center the coefficients. */
    bn.subvm.8s w6, w5, w6

    loopi 8, 13
      /* Shift in one 20-bit coefficient into w0-w4. */
      bn.rshi w0, w1, w0 >> 20
      bn.rshi w1, w2, w1 >> 20
      bn.rshi w2, w3, w2 >> 20
      bn.rshi w3, w4, w3 >> 20
      bn.rshi w4, w6, w4 >> 20

      /* Shift out the processed coefficient from w6-w13. */
      bn.rshi  w6,  w7,  w6 >> 32
      bn.rshi  w7,  w8,  w7 >> 32
      bn.rshi  w8,  w9,  w8 >> 32
      bn.rshi  w9, w10,  w9 >> 32
      bn.rshi w10, w11, w10 >> 32
      bn.rshi w11, w12, w11 >> 32
      bn.rshi w12, w13, w12 >> 32
      bn.rshi w13, w31, w13 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the bit-packed coefficients to DMEM. */
  addi x4, x0, 0
  bn.sid x4++, 0(x3)
  bn.sid x4++, 32(x3)
  bn.sid x4++, 64(x3)
  bn.sid x4++, 96(x3)
  bn.sid x4++, 128(x3)
  addi x3, x3, 160

  ret

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
 * @param[in] x3: DMEM pointer to second Boolean share of the encode S.
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

  /* In each iteration, we decode 8 Boolean-shared coefficients that are
     bit-unpacked and converted to arithmetic shares in w0 and w1. */
  loopi 8, 14
    loopi 8, 7
      /* Share 0: */

      /* Shift in a 3-bit chunk into w0. */
      bn.rshi w0, w9, w0 >> 3
      bn.rshi w0, w31, w0 >> 29
      /* Remove the processed 3-bit chunk from w9. */
      bn.rshi w9, w31, w9 >> 3

      /* Share 1: */

      bn.xor w31, w31, w31 /* dummy */

      /* Shift in a 3-bit chunk into w1. */
      bn.rshi w1, w10, w1 >> 3
      bn.rshi w1, w31, w1 >> 29
      /* Remove the processed 3-bit chunk from w10. */
      bn.rshi w10, w31, w10 >> 3
      /* End of loop */

    /* Finalize the bit unpacking by converting the 8 coefficients to
       arithmetic shares and computing the subtraction ETA - x mod Q. */

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
