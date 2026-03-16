/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines for different representations. */

.globl decode_z

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

    jal x1, _bit_unpack_z_8x32

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
_bit_unpack_z_8x32:
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
