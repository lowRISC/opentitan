/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Byte encoding and compression subroutines (ByteEncode_d, Compress_d) for ML-KEM-1024 (q = 3329). */

.globl encode_12
.globl encode_11
.globl encode_5
.globl encode_1
.globl compress_11
.globl compress_5
.globl compress_1

.text

/**
 * Vectorized encoding of 256 12-bit polynomial coefficients into 384 packed bytes (ByteEncode_12).
 *
 * Implements Algorithm 5 (ByteEncode_d) of FIPS 203 for d = 12.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to pack 256 12-bit coefficients into 12 256-bit WDRs.
 * Loop 32 iterations: 256 coefficients -> 384 bytes output.
 *
 * @param[in]  x2: DMEM input address of 256 32-bit polynomial coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 384 packed bytes (12 256-bit WDRs).
 *
 */
encode_12:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  loopi 32, 16
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    loopi 8, 13
      bn.rshi w1,  w2,  w1  >> 12
      bn.rshi w2,  w3,  w2  >> 12
      bn.rshi w3,  w4,  w3  >> 12
      bn.rshi w4,  w5,  w4  >> 12
      bn.rshi w5,  w6,  w5  >> 12
      bn.rshi w6,  w7,  w6  >> 12
      bn.rshi w7,  w8,  w7  >> 12
      bn.rshi w8,  w9,  w8  >> 12
      bn.rshi w9,  w10, w9  >> 12
      bn.rshi w10, w11, w10 >> 12
      bn.rshi w11, w12, w11 >> 12
      bn.rshi w12, w0,  w12 >> 12

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the 12 encoded WDRs (384 bytes) to DMEM at x3 from w1 up to w12. */
  addi x4, x0, 1
  loopi 12, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Vectorized encoding of 256 11-bit polynomial coefficients into 352 packed bytes (ByteEncode_11).
 *
 * Implements Algorithm 5 (ByteEncode_d) of FIPS 203 for d = 11.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to pack 256 11-bit coefficients into 11 256-bit WDRs.
 * Loop 32 iterations: 256 coefficients -> 352 bytes output.
 *
 * @param[in]  x2: DMEM input address of 256 32-bit coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 352 packed bytes (11 256-bit WDRs).
 *
 */
encode_11:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  loopi 32, 15
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    loopi 8, 12
      bn.rshi w1,  w2,  w1  >> 11
      bn.rshi w2,  w3,  w2  >> 11
      bn.rshi w3,  w4,  w3  >> 11
      bn.rshi w4,  w5,  w4  >> 11
      bn.rshi w5,  w6,  w5  >> 11
      bn.rshi w6,  w7,  w6  >> 11
      bn.rshi w7,  w8,  w7  >> 11
      bn.rshi w8,  w9,  w8  >> 11
      bn.rshi w9,  w10, w9  >> 11
      bn.rshi w10, w11, w10 >> 11
      bn.rshi w11, w0,  w11 >> 11

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the 11 encoded WDRs (352 bytes) to DMEM at x3 from w1 up to w11. */
  addi x4, x0, 1
  loopi 11, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Compress 256 coefficients mod 3329 to 11 bits and encode (Compress_11).
 *
 * Implements Section 4.2.1 (Compress_d) of FIPS 203 for d = 11.
 * x' = ((x * 2048 + 1664) * 1290168 >> 32) mod 2048.
 *
 * @param[in]  x2: DMEM input address of 256 polynomial coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 352 compressed/packed bytes (11 WDRs).
 *
 */
compress_11:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Setup MOD CSR and w0 with reciprocal constant M = 1290168 and mu = 0. */
  la x5, _compress_recip_m
  bn.lid x0, 0(x5)
  bn.wsrw 0, w0

  /* Setup w30 = [1664, 1664, ..., 1664] (offset for rounding). */
  li x4, 30
  la x5, _compress_offset_1664
  bn.lid x4, 0(x5)

  /* Setup w29 = [0x7FF, 0x7FF, ..., 0x7FF] (11-bit mask). */
  bn.not w29, w31
  bn.shv.8s w29, w29 >> 21

  /* x7 = input address x2, x4 = WDR index 1 (w1). */
  addi x7, x2, 0
  li x4, 1

  /* Vectorized loop: process 256 coefficients in 32 iterations (8 per iteration). */
  loopi 32, 6
    bn.lid x4, 0(x7)
    bn.shv.8s w1, w1 << 11
    bn.addv.8s w1, w1, w30
    bn.mulvml.8s w1, w1, w0, 0
    bn.and w1, w1, w29
    bn.sid x4, 0(x7++)
    /* End of loop */

  /* Restore x2 and x3 before calling encode_11. */
  lw x2, -20(x31)
  lw x3, -16(x31)
  jal x1, encode_11

  /* Restore MOD CSR to q = 3329, mu = 0x94570CFF. */
  la x5, _compress_modulus_3329
  bn.lid x0, 0(x5)
  bn.wsrw 0, w0

  /* Restore GPRs. */
  .irp reg, x7, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Vectorized encoding of 256 5-bit polynomial coefficients into 160 packed bytes (ByteEncode_5).
 *
 * Implements Algorithm 5 (ByteEncode_d) of FIPS 203 for d = 5.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to pack 256 5-bit coefficients into 5 256-bit WDRs.
 * Loop 32 iterations: 256 coefficients -> 160 bytes output.
 *
 * @param[in]  x2: DMEM input address of 256 32-bit coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 160 packed bytes (5 256-bit WDRs).
 *
 */
encode_5:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  loopi 32, 9
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    loopi 8, 6
      bn.rshi w1, w2, w1 >> 5
      bn.rshi w2, w3, w2 >> 5
      bn.rshi w3, w4, w3 >> 5
      bn.rshi w4, w5, w4 >> 5
      bn.rshi w5, w0, w5 >> 5

      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the 5 encoded WDRs (160 bytes) to DMEM at x3 from w1 up to w5. */
  addi x4, x0, 1
  loopi 5, 2
    bn.sid x4++, 0(x3)
    addi x3, x3, 32
    /* End of loop */

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Compress 256 coefficients mod 3329 to 5 bits and encode (Compress_5).
 *
 * Implements Section 4.2.1 (Compress_d) of FIPS 203 for d = 5.
 * x' = ((x * 32 + 1664) * 1290168 >> 32) mod 32.
 *
 * @param[in]  x2: DMEM input address of 256 polynomial coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 160 compressed/packed bytes (5 WDRs).
 *
 */
compress_5:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Setup MOD CSR and w0 with reciprocal constant M = 1290168 and mu = 0. */
  la x5, _compress_recip_m
  bn.lid x0, 0(x5)
  bn.wsrw 0, w0

  /* Setup w30 = [1664, 1664, ..., 1664] (offset for rounding). */
  li x4, 30
  la x5, _compress_offset_1664
  bn.lid x4, 0(x5)

  /* Setup w29 = [0x1F, 0x1F, ..., 0x1F] (5-bit mask). */
  bn.not w29, w31
  bn.shv.8s w29, w29 >> 27

  /* x7 = input address x2, x4 = WDR index 1 (w1). */
  addi x7, x2, 0
  li x4, 1

  /* Vectorized loop: process 256 coefficients in 32 iterations (8 per iteration). */
  loopi 32, 6
    bn.lid x4, 0(x7)
    bn.shv.8s w1, w1 << 5
    bn.addv.8s w1, w1, w30
    bn.mulvml.8s w1, w1, w0, 0
    bn.and w1, w1, w29
    bn.sid x4, 0(x7++)
    /* End of loop */

  /* Restore x2 and x3 before calling encode_5. */
  lw x2, -20(x31)
  lw x3, -16(x31)
  jal x1, encode_5

  /* Restore MOD CSR to q = 3329, mu = 0x94570CFF. */
  la x5, _compress_modulus_3329
  bn.lid x0, 0(x5)
  bn.wsrw 0, w0

  /* Restore GPRs. */
  .irp reg, x7, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Compress 256 coefficients to 1 bit per coefficient (Compress_1).
 *
 * Implements Section 4.2.1 (Compress_d) of FIPS 203 for d = 1.
 * x' = ((x * 2 + 1664) * 1290168 >> 32) mod 2.
 *
 * @param[in]  x2: DMEM input address of 256 32-bit polynomial coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 256 32-bit words (0 or 1 per word).
 *
 */
compress_1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6, x7
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Setup MOD CSR and w0 with reciprocal constant M = 1290168 and mu = 0. */
  la x5, _compress_recip_m
  bn.lid x0, 0(x5)
  bn.wsrw 0, w0

  /* Setup w30 = [1664, 1664, ..., 1664] (offset for rounding). */
  li x4, 30
  la x5, _compress_offset_1664
  bn.lid x4, 0(x5)

  /* Setup w29 = [0x1, 0x1, ..., 0x1] (1-bit mask). */
  bn.not w29, w31
  bn.shv.8s w29, w29 >> 31

  /* x6 = input address x2, x7 = output address x3, x4 = WDR index 1 (w1). */
  addi x6, x2, 0
  addi x7, x3, 0
  li x4, 1

  /* Vectorized loop: process 256 coefficients in 32 iterations (8 per iteration). */
  loopi 32, 6
    bn.lid x4, 0(x6++)
    bn.shv.8s w1, w1 << 1
    bn.addv.8s w1, w1, w30
    bn.mulvml.8s w1, w1, w0, 0
    bn.and w1, w1, w29
    bn.sid x4, 0(x7++)
    /* End of loop */

  /* Restore MOD CSR to q = 3329, mu = 0x94570CFF. */
  la x5, _compress_modulus_3329
  bn.lid x0, 0(x5)
  bn.wsrw 0, w0

  /* Restore GPRs. */
  .irp reg, x7, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret


/**
 * Vectorized encoding of 256 1-bit coefficients into 32 packed bytes (ByteEncode_1).
 *
 * Implements Algorithm 5 (ByteEncode_d) of FIPS 203 for d = 1.
 * Uses 256-bit WDR vector funnel shifts (`bn.rshi`) to pack 256 1-bit coefficients into 1 256-bit WDR.
 * Loop 32 iterations: 256 coefficients -> 32 bytes output.
 *
 * @param[in]  x2: DMEM input address of 256 32-bit polynomial coefficients (1024 bytes).
 * @param[in]  x3: DMEM output address for 32 packed bytes (1 WDR).
 *
 */
encode_1:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  loopi 32, 5
    /* Load 8 coefficients into w0. */
    bn.lid x0, 0(x2++)

    loopi 8, 2
      bn.rshi w1, w0, w1 >> 1
      /* Remove the coefficient from w0. */
      bn.rshi w0, w31, w0 >> 32
      /* End of loop */
    nop
    /* End of loop */

  /* Store the 1 encoded WDR (32 bytes) to DMEM at x3. */
  li x4, 1
  bn.sid x4, 0(x3)

  /* Restore registers. */
  .irp reg, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
