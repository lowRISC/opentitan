/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Byte decoding and decompression subroutines (ByteDecode_d, Decompress_d) for ML-KEM-1024 (q = 3329). */

.globl decode_12
.globl decode_11
.globl decode_5
.globl decode_1
.globl decompress_11
.globl decompress_5

.text

/**
 * Decode 384 bytes into 256 12-bit polynomial coefficients (ByteDecode_12).
 *
 * Implements Algorithm 6 (ByteDecode_d) of FIPS 203 for d = 12.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to unpack 12 256-bit WDRs (384 bytes)
 * into 256 32-bit polynomial coefficients.
 *
 * @param[in]  x2: DMEM input address of 384 packed bytes (12 WDRs).
 * @param[in]  x3: DMEM output address for 256 32-bit polynomial coefficients (1024 bytes).
 *
 */
decode_12:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load 12 WDRs (384 bytes) into w12..w1 from input at x2. */
  addi x4, x0, 12
  loopi 12, 2
    bn.lid x4, 0(x2++)
    addi x4, x4, -1
    /* End of loop */

  /* Unpack 256 12-bit coefficients into 32 256-bit WDRs (1024 bytes) at x3. */
  loopi 32, 16
    loopi 8, 14
      bn.rshi w0,  w12, w0  >> 12
      bn.rshi w0,  w31, w0  >> 20
      bn.rshi w12, w11, w12 >> 12
      bn.rshi w11, w10, w11 >> 12
      bn.rshi w10, w9,  w10 >> 12
      bn.rshi w9,  w8,  w9  >> 12
      bn.rshi w8,  w7,  w8  >> 12
      bn.rshi w7,  w6,  w7  >> 12
      bn.rshi w6,  w5,  w6  >> 12
      bn.rshi w5,  w4,  w5  >> 12
      bn.rshi w4,  w3,  w4  >> 12
      bn.rshi w3,  w2,  w3  >> 12
      bn.rshi w2,  w1,  w2  >> 12
      bn.rshi w1,  w31, w1  >> 12
      /* End of loop */

    bn.sid x0, 0(x3++)
    /* End of loop */

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Decode 352 bytes into 256 11-bit polynomial coefficients (ByteDecode_11).
 *
 * Implements Algorithm 6 (ByteDecode_d) of FIPS 203 for d = 11.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to unpack 11 256-bit WDRs (352 bytes)
 * into 256 32-bit polynomial coefficients.
 *
 * @param[in]  x2: DMEM input address of 352 packed bytes (11 WDRs).
 * @param[in]  x3: DMEM output address for 256 32-bit polynomial coefficients (1024 bytes).
 *
 */
decode_11:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load 11 WDRs (352 bytes) into w11..w1 from input at x2. */
  addi x4, x0, 11
  loopi 11, 2
    bn.lid x4, 0(x2++)
    addi x4, x4, -1
    /* End of loop */

  /* Unpack 256 11-bit coefficients into 32 256-bit WDRs (1024 bytes) at x3. */
  loopi 32, 15
    loopi 8, 13
      bn.rshi w0,  w11, w0  >> 11
      bn.rshi w0,  w31, w0  >> 21
      bn.rshi w11, w10, w11 >> 11
      bn.rshi w10, w9,  w10 >> 11
      bn.rshi w9,  w8,  w9  >> 11
      bn.rshi w8,  w7,  w8  >> 11
      bn.rshi w7,  w6,  w7  >> 11
      bn.rshi w6,  w5,  w6  >> 11
      bn.rshi w5,  w4,  w5  >> 11
      bn.rshi w4,  w3,  w4  >> 11
      bn.rshi w3,  w2,  w3  >> 11
      bn.rshi w2,  w1,  w2  >> 11
      bn.rshi w1,  w31, w1  >> 11
      /* End of loop */

    bn.sid x0, 0(x3++)
    /* End of loop */

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Decompress 352 bytes into 256 coefficients mod 3329 (Decompress_11).
 *
 * Implements Section 4.2.1 (Decompress_d) of FIPS 203 for d = 11.
 * y = round(x * 3329 / 2048) = (x * 3329 + 1024) >> 11.
 *
 * @param[in]  x2: DMEM input address of 352 packed bytes.
 * @param[in]  x3: DMEM output address for 256 32-bit polynomial coefficients (1024 bytes).
 *
 */
decompress_11:
  .irp reg, x2, x3, x4, x5, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  jal x1, decode_11

  /* Set output address x7 from x3. */
  addi x7, x3, 0

  /* Setup w30 = [1024, 1024, ..., 1024] (offset for rounding). */
  li x4, 30
  la x5, _decompress_offset_1024
  bn.lid x4, 0(x5)

  /* Read q = 3329 from MOD CSR (MOD[31:0] = 3329) into w29[0]. */
  bn.wsrr w29, 0

  /* Vectorized loop: process 256 coefficients in 32 iterations (8 per iteration).
     Computes Decompress_11(x) = round(x * 3329 / 2^11) = ((x * 3329) + 1024) >> 11.
     x * 3329 is computed via bn.mulvl.8s using q = 3329 from MOD CSR (w29[0]). */
  li x4, 1
  loopi 32, 5
    bn.lid x4, 0(x7)
    bn.mulvl.8s w1, w1, w29, 0
    bn.addv.8s w1, w1, w30
    bn.shv.8s w1, w1 >> 11
    bn.sid x4, 0(x7++)
    /* End of loop */

  .irp reg, x7, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Decode 160 bytes into 256 5-bit polynomial coefficients (ByteDecode_5).
 *
 * Implements Algorithm 6 (ByteDecode_d) of FIPS 203 for d = 5.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to unpack 5 256-bit WDRs (160 bytes)
 * into 256 32-bit polynomial coefficients.
 *
 * @param[in]  x2: DMEM input address of 160 packed bytes (5 WDRs).
 * @param[in]  x3: DMEM output address for 256 32-bit polynomial coefficients (1024 bytes).
 *
 */
decode_5:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load 5 WDRs (160 bytes) into w5..w1 from input at x2. */
  addi x4, x0, 5
  loopi 5, 2
    bn.lid x4, 0(x2++)
    addi x4, x4, -1
    /* End of loop */

  /* Unpack 256 5-bit coefficients into 32 256-bit WDRs (1024 bytes) at x3. */
  loopi 32, 9
    loopi 8, 7
      bn.rshi w0, w5, w0 >> 5
      bn.rshi w0, w31, w0 >> 27
      bn.rshi w5, w4, w5 >> 5
      bn.rshi w4, w3, w4 >> 5
      bn.rshi w3, w2, w3 >> 5
      bn.rshi w2, w1, w2 >> 5
      bn.rshi w1, w31, w1 >> 5
      /* End of loop */

    bn.sid x0, 0(x3++)
    /* End of loop */

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Decompress 160 bytes into 256 coefficients mod 3329 (Decompress_5).
 *
 * Implements Section 4.2.1 (Decompress_d) of FIPS 203 for d = 5.
 * y = round(x * 3329 / 32) = (x * 3329 + 16) >> 5.
 *
 * @param[in]  x2: DMEM input address of 160 packed bytes.
 * @param[in]  x3: DMEM output address for 256 32-bit polynomial coefficients (1024 bytes).
 *
 */
decompress_5:
  .irp reg, x2, x3, x4, x5, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  jal x1, decode_5

  /* Set output address x7 from x3. */
  addi x7, x3, 0

  /* Setup w30 = [16, 16, ..., 16] (offset for rounding). */
  li x4, 30
  la x5, _decompress_offset_16
  bn.lid x4, 0(x5)

  /* Read q = 3329 from MOD CSR (MOD[31:0] = 3329) into w29[0]. */
  bn.wsrr w29, 0

  /* Vectorized loop: process 256 coefficients in 32 iterations (8 per iteration).
     Computes Decompress_5(x) = round(x * 3329 / 2^5) = ((x * 3329) + 16) >> 5.
     x * 3329 is computed via bn.mulvl.8s using q = 3329 from MOD CSR (w29[0]). */
  li x4, 1
  loopi 32, 5
    bn.lid x4, 0(x7)
    bn.mulvl.8s w1, w1, w29, 0
    bn.addv.8s w1, w1, w30
    bn.shv.8s w1, w1 >> 5
    bn.sid x4, 0(x7++)
    /* End of loop */

  .irp reg, x7, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Decode 32 packed bytes into 256 1-bit polynomial coefficients (ByteDecode_1).
 *
 * Implements Algorithm 6 (ByteDecode_d) of FIPS 203 for d = 1.
 * Unpacks 32-byte binary stream into 256 polynomial coefficients over Z_q:
 *   If bit i == 1 -> f[i] = (q + 1) / 2 = 1665
 *   If bit i == 0 -> f[i] = 0
 *
 * @param[in]  x2: DMEM input address of 32 packed bytes (1 WDR).
 * @param[in]  x3: DMEM output address for 256 32-bit polynomial coefficients (1024 bytes).
 *
 */
decode_1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load 1 WDR (32 bytes) into w1. */
  li x4, 1
  bn.lid x4, 0(x2)

  /* Load constant vector w2 = [1665, 1665, ..., 1665] from DMEM. */
  li x4, 2
  la x5, _decompress_const_1665
  bn.lid x4, 0(x5)

  /* Unpack 256 1-bit coefficients into 32 256-bit WDRs (1024 bytes) at x3. */
  loopi 32, 7
    loopi 8, 3
      bn.rshi w0, w1, w0 >> 1
      bn.rshi w0, w31, w0 >> 31
      bn.rshi w1, w31, w1 >> 1
      /* End of loop */

    /* Create 0x00000000 / 0xFFFFFFFF mask, and mask with 1665. */
    bn.subv.8s w0, w31, w0
    bn.and w0, w0, w2
    bn.sid x0, 0(x3++)
    /* End of loop */

  /* Restore registers. */
  .irp reg, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
