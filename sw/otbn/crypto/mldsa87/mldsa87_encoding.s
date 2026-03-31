/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Polynomial encoding/decoding routines. */

.globl encode_w1

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
