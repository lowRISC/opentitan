/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines for different representations. */

.globl decode_z
.globl decode_t1

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
