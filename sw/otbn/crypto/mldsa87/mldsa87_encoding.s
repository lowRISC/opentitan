/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.include "mldsa87.inc"

/* Polynomial encoding/decoding routines. */

/* Common */
.globl encode_w1
.globl decode_s

/* Keygen */
.globl encode_t0
.globl encode_t1
.globl encode_s

/* Sign */
.globl decode_t0
.globl decode_w1
.globl encode_z

/* Verify */
.globl decode_z
.globl decode_t1
.globl decode_h

.text

/**
 * Encode a W1 polynomial into a dense representation.
 *
 * A W1 polynomial consists of 256 4-bit coefficients hence its encoded
 * representation has a size of 256 * 4 = 1024 bits or 128 bytes. This routine
 * implements the `w1Encode` function (Algorithm 28) of FIPS-204.
 *
 * @param[in] x2: DMEM location of the decoded W1 polynomial.
 * @param[in] x3: DMEM location of the encoded W1 polynomial.
 */
encode_w1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* w1 is encoded in chunks of 64 32-bit coefficients that fit in a single
    256-bit WDR. */
  loopi 4, 11
    /* Load and unpack 64 32-bit coefficients into w0-w7. */
    addi x20, x0, 0
    bn.lid x20++, 0(x2)
    bn.lid x20++, 32(x2)
    bn.lid x20++, 64(x2)
    bn.lid x20++, 96(x2)
    bn.lid x20++, 128(x2)
    bn.lid x20++, 160(x2)
    bn.lid x20++, 192(x2)
    bn.lid x20++, 224(x2)

    /* Encode the 64 32-bit coefficients into a single WDR. */
    jal x1, _simple_bit_pack_w1_64x32_64x4

    addi x2, x2, 256
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Encode the 64 32-bit coefficients into 64 4-bit coefficients in a
 * single WDR w8. This subroutine is akin to the `SimpleBitPack` function
 * (Algorithm 16) of FIPS-204.
 */
_simple_bit_pack_w1_64x32_64x4:
  /* Set up WDR pointers for intermediate results. */
  addi x4, x0, 0
  addi x5, x0, 8

  /* Iterate over w0-w7. */
  loopi 8, 5
    bn.movr x0, x4++
    loopi 8, 2
      /* Shift out the least significant 4 bits into w8 and remove it from w0. */
      bn.rshi w8, w0, w8 >> 4
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */
  bn.sid x5, 0(x3++)
  ret

/* Polynomial decoding routines. */

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

  /* Initialize the WDRs that hold intermediate results with randomness. */
  bn.wsrr w0, URND
  bn.wsrr w1, URND

  /* In each iteration, we decode 8 Boolean-shared coefficients that are
     bit-unpacked and converted to arithmetic shares in w0 and w1. */
  loopi 8, 19
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

/* Polynomial encoding/decoding routines for ML-DSA-87 keygen. */

.text

/**
 * Encode a T0 polynomial into a dense representation.
 *
 * A T0 of the secret key consists of 256 13-bit coefficients in the range
 * ]-2^12, 2^12] hence its encoded representation has a size of
 * 256 * 13 = 3328 bits or 416 bytes. This routine is a part of the `skEncode`
 * function (Algorithm 24) of FIPS-204.
 *
 * @param[in] x2: DMEM location of the decoded T0 polynomial.
 * @param[in] x3: DMEM location of the encoded T0 polynomial.
 */
encode_t0:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Prepare subtraction vector w2 = b = (2^12, 2^12, ..., 2^12). */
  bn.not w1, w31
  bn.shv.8s w1, w1 >> 31
  bn.shv.8s w1, w1 << 12

  /*
   * We have 3328 = 13 * 256, hence all 256 13-bit coefficients exactly fit in
   * 13 WDRs. Iterate in chunks of 8 coefficients over the polynomial and shift
   * each coefficient into w2-w14 to form the encoded representation.
   */

  loopi 32, 18
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    /* Compute b - x mod Q for each coefficient x in w0. This is the centering
       step of the `BitPack` function (Algorithm 17) of FIPS-204. */
    bn.subvm.8S w0, w1, w0

    loopi 8, 14
      /* Shift each 13-bit coefficient into w2-w14. */
      bn.rshi w2, w3, w2 >> 13
      bn.rshi w3, w4, w3 >> 13
      bn.rshi w4, w5, w4 >> 13
      bn.rshi w5, w6, w5 >> 13
      bn.rshi w6, w7, w6 >> 13
      bn.rshi w7, w8, w7 >> 13
      bn.rshi w8, w9, w8 >> 13
      bn.rshi w9, w10, w9 >> 13
      bn.rshi w10, w11, w10 >> 13
      bn.rshi w11, w12, w11 >> 13
      bn.rshi w12, w13, w12 >> 13
      bn.rshi w13, w14, w13 >> 13
      bn.rshi w14, w0, w14 >> 13

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the encoded polynomial in w2-w14 to DMEM. */
  addi x4, x0, 2
  loopi 13, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Encode a T1 polynomial into a dense representation.
 *
 * A T1 of the public key consists of 256 10-bit coefficients in the range
 * [0, 2^10-1] hence its encoded representation has a size of 256 * 10 = 2560
 * bits or 320 bytes. This routine is a part of the `pkEncode` function
 * (Algorithm 22) of FIPS-204.
 *
 * @param[in] x2: DMEM location of the decoded T1 polynomial.
 * @param[in] x3: DMEM location of the encoded T1 polynomial.
 */
encode_t1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /*
   * We have 2560 = 10 * 256, hence all 256 10-bit coefficients exactly fit in
   * 10 WDRs. Iterate in chunks of 8 coefficients over the polynomial and shift
   * each coefficient into w1-w10 to form the encoded representation.
   */

  loopi 32, 14
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    loopi 8, 11
      /* Shift each 10-bit coefficient into w1-w10. */
      bn.rshi w1, w2, w1 >> 10
      bn.rshi w2, w3, w2 >> 10
      bn.rshi w3, w4, w3 >> 10
      bn.rshi w4, w5, w4 >> 10
      bn.rshi w5, w6, w5 >> 10
      bn.rshi w6, w7, w6 >> 10
      bn.rshi w7, w8, w7 >> 10
      bn.rshi w8, w9, w8 >> 10
      bn.rshi w9, w10, w9 >> 10
      bn.rshi w10, w0, w10 >> 10

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the encoded polynomial in w1-w10 to DMEM. */
  addi x4, x0, 1
  loopi 10, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Encode a S{1, 2} polynomial to a dense representation.
 *
 * A S{1, 2} polynomial of the secret key consists of 256 3-bit coefficients in
 * the range [-ETA, ETA] for ETA = 2, hence its encoded representation has a
 * size of 256 * 3 = 768 bits or 96 bytes. This routine is a part of the
 * `skEncode` function (Algorithm 24) of FIPS-204.
 *
 * The S polynomial is assumed to be passed as two arithmetic shares. The
 * encoded polynomial is returned as two Boolean shares.
 *
 * @param[in] x2: DMEM address of the first arithmetic share of S.
 * @param[in] x3: DMEM address of the second arithmetic share of S.
 * @param[in] x4: DMEM address of the first Boolean share of the encoded S.
 * @param[in] x5: DMEM address of the second Boolean share of the encoded S.
 */
encode_s:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Set up subtraction vector w2 = [ETA, ETA, ..., ETA]. */
  bn.not w2, w31
  bn.shv.8s w2, w2 >> 31
  bn.shv.8s w2, w2 << 1

  /* WDR pointers. */
  addi x6, x0, 0
  addi x7, x0, 1

  /* Initialize the registers that hold the compressed polynomial shares with
     randomness. This avoids isolating secrets bits in an all-zero register
     during the shifting operations. */

  /* Share 0. */
  bn.wsrr w3, URND
  bn.wsrr w4, URND
  bn.wsrr w5, URND
  /* Share 1. */
  bn.wsrr w6, URND
  bn.wsrr w7, URND
  bn.wsrr w8, URND

  /* Encode the polynomial in chunks of 8 coefficients at a time. */
  loopi 32, 19
    /* Load the two arithmetically shared vectors of 8 coefficients
       x = (x0, x1) and compute ETA - x mod Q. This is the centering step of
       the `BitPack` function (Algorithm 17) of FIPS-204. */

    /* Share 0. */
    bn.lid x6, 0(x2++)
    bn.subvm.8S w0, w2, w0

    bn.xor w31, w31, w31 /* dummy */

    /* Share 1. */
    bn.lid x7, 0(x3++)
    bn.subvm.8S w1, w31, w1

    /* Convert the two arithmetically shared vectors to Boolean shares. */
    jal x1, sec_a2b_8x32

    loopi 8, 11
      /* Randomness to shift into registers when a coefficient is extracted.
         This avoids that few secrets bits are isolated in an all-zero WDR. */
      bn.wsrr w9, URND
      bn.wsrr w10, URND

      /* Share 0: */

      /* Shift a 3-bit coefficient into w3-w5. */
      bn.rshi w3, w4, w3 >> 3
      bn.rshi w4, w5, w4 >> 3
      bn.rshi w5, w0, w5 >> 3
      bn.rshi w0, w9, w0 >> 32

      /* Share 1. */

      bn.xor w31, w31, w31 /* dummy */

      /* Shift a 3-bit coefficient into w6-w8. */
      bn.rshi w6, w7, w6 >> 3
      bn.rshi w7, w8, w7 >> 3
      bn.rshi w8, w1, w8 >> 3
      bn.rshi w1, w10, w1 >> 32
      /* End of loop */

    nop
    /* End of loop */

  /* Store the encoded polynomial shares to DMEM. */

  /* Share 0. */
  addi x6, x0, 3
  bn.sid x6++, 0(x4)
  bn.sid x6++, 32(x4)
  bn.sid x6++, 64(x4)

  bn.xor w31, w31, w31 /* dummy */

  /* Share 1. */
  bn.sid x6++, 0(x5)
  bn.sid x6++, 32(x5)
  bn.sid x6++, 64(x5)

  /* Restore clobbered general-purpose registers. */
  .irp reg, x7, x6, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/* Polynomial encoding/decoding routines for ML-DSA-87 sign. */

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

/* Verify-specific encoding routines. */

.text

/**
 * Decode a Z signature polynomial to the canonical representation.
 *
 * An encoded Z polynomial consists of 256 20-bit (5120 bits or 640 bytes in
 * total) coefficients in the interval ]-GAMMA1, GAMMA1]. Every coefficient
 * is mapped to a 32-bit slot in the decoded polymomial occupying 1024 bytes.
 *
 * This routine implements the `BitUnpack` function (Algorithm 19) as part of
 * `sigDecode` (Algorithm 27) in FIPS-204.
 *
 * @param[in] x2: DMEM pointer to the encoded polynomial Z (640 bytes).
 * @param[in] x3: DMEM pointer to the decoded polynomial Z (1024 bytes).
 */
decode_z:
  /* Push clobbered registers onto the stack. */
  .irp reg, x3, x4, x5, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Prepare subtraction vector GAMMA1 = 2^19:
     w13 = [2^19, 2^19, 2^19, 2^19, 2^19, 2^19, 2^19, 2^19]. */
  bn.not w13, w31
  bn.shv.8s w13, w13 >> 31
  bn.shv.8s w13, w13 << 19

  /*
   * Decode the polynomial in steps of 64 coefficients. In each iteration,
   * 64*20=1280 bits from the undecoded t1 are extracted and processed. These
   * 1280 bits fit in 5 WDRs w8-w12.
   */
  addi x4, x0, 8
  addi x5, x2, 0
  loopi 4, 8
    bn.lid x4++, 0(x5)
    bn.lid x4++, 32(x5)
    bn.lid x4++, 64(x5)
    bn.lid x4++, 96(x5)
    bn.lid x4++, 128(x5)

    jal x1, _bit_unpack_z_8x8

    addi x4, x0, 8
    addi x5, x5, 160
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x7, x6, x5, x4, x3
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Extract 1280 bits (64 20-bit coefficients) from w8-w12 and expand them into
 * 64 32-bit coefficients in the range ]-GAMMA1, GAMMA1].
 */
_bit_unpack_z_8x8:
  /* Setup WDR pointers. */
  li x6, 0
  li x7, 14

  /* Extract 64 20-bit chunks into 8 WDRs (w0-w7) containing 8 32-bit
     coefficients each. */
  loopi 8, 10
    loopi 8, 7
      /* Shift a 20-bit chunk into the most significant 32-bit coefficient. */
      bn.rshi w14,  w8, w14 >> 20
      bn.rshi w14, w31, w14 >> 12
      /* Remove the unpacked 20-bit chunk from w8-w12. */
      bn.rshi  w8,  w9,  w8 >> 20
      bn.rshi  w9, w10,  w9 >> 20
      bn.rshi w10, w11, w10 >> 20
      bn.rshi w11, w12, w11 >> 20
      bn.rshi w12, w31, w12 >> 20
      /* End of loop */

    /* Compute GAMMA1 - x mod q for eight 32-bit coefficients. */
    bn.subvm.8S w14, w13, w14
    bn.movr x6++, x7
    /* End of loop */

  /* w0-w8 contain the 64 32-bit centered coefficients. */
  addi x20, x0, 0
  bn.sid x20++, 0(x3)
  bn.sid x20++, 32(x3)
  bn.sid x20++, 64(x3)
  bn.sid x20++, 96(x3)
  bn.sid x20++, 128(x3)
  bn.sid x20++, 160(x3)
  bn.sid x20++, 192(x3)
  bn.sid x20++, 224(x3)
  addi x3, x3, 256

  ret

/**
 * Decode a T1 polynomial of the public key to the canonical representation.
 *
 * An encoded T1 polynomial consists of 256 10-bit (2560 bits or 320 bytes in
 * total) coefficients in the interval [0, 2^10-1].  Every coefficient is
 * mapped to a 32-bit slot in the decoded polymomial occupying 1024 bytes.
 *
 * This routine implements the `SimpleBitUnpack` function (Algorithm 18) as
 * part of `pkDecode` (Algorithm 23) in FIPS-204.
 *
 * @param[in] x2: DMEM pointer to the encoded polynomial T1 (320 bytes).
 * @param[in] x3: DMEM pointer to the decoded polynomial T1 (1024 bytes).
 */
decode_t1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x3, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* An undecoded t1 polynomial is 256*10=2560 bits or 10 256-bit words.
     Load them here into w4-w13. */
  addi x4, x0, 4
  addi x5, x2, 0
  loopi 10, 2
    bn.lid x4, 0(x5++)
    addi   x4, x4, 1
    /* End of loop */

  /*
   * Decode the polynomial in steps of 32 coefficients. In each iteration,
   * 32*10=320 bits from the undecoded T1 polynomial are extracted and
   * processed.
   */

  /* Bit unpack the first 320 bits. */
  bn.mov w14, w4
  bn.mov w15, w5
  jal x1, _simple_bit_unpack_t1_4x8

  /* 192 bits left in w5. */
  bn.rshi w14, w6, w5 >> 64
  bn.rshi w15, w7, w6 >> 64
  jal x1, _simple_bit_unpack_t1_4x8

  /* 128 bits left in w6. */
  bn.rshi w14, w7, w6 >> 128
  bn.rshi w15, w8, w7 >> 128
  jal x1, _simple_bit_unpack_t1_4x8

  /* 64 bits left in w7. */
  bn.rshi w14, w8, w7 >> 192
  bn.rshi w15, w9, w8 >> 192
  jal x1, _simple_bit_unpack_t1_4x8

  /* 256 bits left in w9. */
  bn.mov w14, w9
  bn.mov w15, w10
  jal x1, _simple_bit_unpack_t1_4x8

  /* 192 bits left in w10. */
  bn.rshi w14, w11, w10 >> 64
  bn.rshi w15, w12, w11 >> 64
  jal x1, _simple_bit_unpack_t1_4x8

  /* 128 bits left in w11. */
  bn.rshi w14, w12, w11 >> 128
  bn.rshi w15, w13, w12 >> 128
  jal x1, _simple_bit_unpack_t1_4x8

  /* 64 bits left in w12. */
  bn.rshi w14, w13, w12 >> 192
  bn.rshi w15, w14, w13 >> 192
  jal x1, _simple_bit_unpack_t1_4x8

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4, x3
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/*
 * Extract 320 bits (32 10-bit coefficients) from w14 and w15 and expand them
 * into 32 32-bit coefficients in the range [0,1024].
 */
_simple_bit_unpack_t1_4x8:
  /* Setup WDR output pointer and temp pointer. */
  li x5, 0
  li x6, 16

  /* Extract 32 10-bit chunks into 4 WDRs (w0-w3) containing 8 32-bit
     coefficients each. */
  loopi 4, 6
    loopi 8, 4
      /* Shift in a 10-bit chunk into the most significant 32-bit coefficient. */
      bn.rshi w16, w14, w16 >> 10
      bn.rshi w16, w31, w16 >> 22
      /* Remove the unpacked 13-bit chunk from w18, w19. */
      bn.rshi w14, w15, w14 >> 10
      bn.rshi w15, w31, w15 >> 10
      /* End of loop */

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
 * Decode the compressed hint bytes to a canonical polynomial H[k].
 *
 * A hint is a lookup table that specifies the indices of non-zero coefficients
 * in the hint polynomial. It is a vector h of 75 + 8 bytes where the first 75
 * bytes specify the indicies and the last 8 bytes indicate for each of the 8
 * polynomials the position of the last index within the 75 bytes.
 *
 * For example, if h[75 + 0] = a, then the set h[0:a-1] contains all the
 * non-zero indices in the undecoded hint polynomial H[0]. Analogously,
 * if h[75 + 1] = b, then the set h[a:b-1] contains all the non-zero indices
 * in the polynomial H[1].
 *
 * To simplify the decoding process the hint vector h shall be given unfolded
 * where each byte resides in a separate 4-byte DMEM word. Additionally, a
 * zero word is inserted at h[75] such that the full vector consists of 84
 * bytes in a 336-byte DMEM regin. This is an adapted implementation of
 * `HintBitUnpack` (Algorithm 21) of FIPS-204.
 *
 * @param[in] x2: DMEM address of the compressed bytes.
 * @param[in] x3: DMEM address of the computed h[i] (1024 = 4 * 256 bytes).
 * @param[in] x4: Index k, 0 <= k < 8.
 */
decode_h:
  /* Push clobbered registers onto the stack. */
  .irp reg, x4, x5, x6, x7, x8, x9
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* A hint polynomial is very sparse, zeroize it here before the inserting
     the non-zero coefficients. */
  addi x20, x3, 0
  addi x21, x0, 32
  jal x1, zeroize

  /* Fetch the start and end position of the H[k] indices. */
  addi x5, x4, 75
  slli x5, x5, 2
  add  x5, x5, x2
  lw   x6, 0(x5) /* start */
  lw   x7, 4(x5) /* end */

  /* Calculate the number of iterations end - start. */
  sub x7, x7, x6

  /* This is the edge case where the entire hint is 0. */
  beq x7, x0, _decode_h_end

  /* Constant coefficient 1. */
  addi x8, x0, 1

  /* Iterate over all indices in h[start:end]. */
  loop x7, 7
    /* x = h[start+i]. */
    slli x9, x6, 2
    add  x9, x9, x2
    lw   x9, 0(x9)

    /* H[k][x] = H[k][h[start+i] = 1. */
    slli x9, x9, 2
    add x9, x9, x3
    sw x8, 0(x9)

    addi x6, x6, 1
    /* End of loop */

_decode_h_end:

  /* Restore clobbered general-purpose registers. */
  .irp reg, x9, x8, x7, x6, x5, x4
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
