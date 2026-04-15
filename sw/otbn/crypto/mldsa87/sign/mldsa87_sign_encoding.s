/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines for ML-DSA-87 sign. */

.globl decode_t0

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
