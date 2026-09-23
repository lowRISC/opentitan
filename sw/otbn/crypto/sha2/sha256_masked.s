/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl sha256_masked
.globl bswap32_w23
.globl bswap32_mask

.text

/**
 * Masked SHA-256 for OTBN.
 *
 * Processes 512-bit message blocks using 1st-order Boolean masking:
 * - Rather than expanding the 64-word message schedule into DMEM, maintains a
 *   16-word sliding window directly in four wide data registers (w21..w22 for
 *   Share 0 and w11..w12 for Share 1), requiring no DMEM scratch space for W.
 * - Hides Masking Accelerator Interface (MAI) latency by overlapping chained
 *   32-bit Boolean-shared additions (sec_add_start / sec_add_next) with the
 *   message schedule (sigma0/sigma1) and round functions (S0, S1, Ch, Maj).
 * - Isolates Share 0 and Share 1 flag updates across OTBN's two flag groups
 *   (Share 0 on default FG0, Share 1 on FG1) and clears the 256-bit BN ALU
 *   datapath with `bn.xor w31, w31, w31` between share operations to prevent
 *   1st-order transition leakage.
 *
 * @param[in]          x10: Pointer to Share 0 of padded message in DMEM (512 bits per block)
 * @param[in]          x11: Pointer to Share 1 of padded message in DMEM (512 bits per block)
 * @param[in]          x30: Number of message blocks to process
 * @param[in]  state_s0   : Share 0 of initial hash state (256 bits)
 * @param[in]  state_s1   : Share 1 of initial hash state (256 bits)
 * @param[out] state_s0   : Share 0 of final hash state (256 bits)
 * @param[out] state_s1   : Share 1 of final hash state (256 bits)
 */
sha256_masked:
  /* Initialize zero register and 32-bit lane mask w20 <= 0x00...00ffffffff */
  bn.xor   w31, w31, w31
  bn.not   w20, w31
  bn.rshi  w20, w31, w20 >> 224

  li       x21, 0x2F

  /* Load initial state shares into w30 (Share 0) and w29 (Share 1) */
  la       x3, state_s0
  li       x2, 30
  bn.lid   x2, 0(x3)
  la       x3, state_s1
  li       x2, 29
  bn.lid   x2, 0(x3)

  /* Load byte-swap mask into w8 */
  la       x2, bswap32_mask
  li       x3, 8
  bn.lid   x3, 0(x2)

  li       x23, 23
  li       x6,  24

  /* Process each 512-bit message block */
  beq      x30, x0, .L_done
  loop     x30, 13
    /* Load and byte-swap Share 0 (2 WDRs -> w21, w22) */
    li       x5, 21
    loopi    2, 3
      bn.lid   x23, 0(x10++)
      jal      x1, bswap32_w23
      bn.movr  x5++, x6

    /* Load and byte-swap Share 1 (2 WDRs -> w11, w12) */
    li       x5, 11
    loopi    2, 3
      bn.lid   x23, 0(x11++)
      jal      x1, bswap32_w23
      bn.movr  x5++, x6

    bn.wsrr  w24, URND
    /* Process block with fused sliding-window schedule */
    jal      x1, sha256_process_block_masked
    nop
    /* End of block loop */

.L_done:
  /* Write back final state shares */
  la       x3, state_s0
  li       x2, 30
  bn.sid   x2, 0(x3)
  la       x3, state_s1
  li       x2, 29
  bn.sid   x2, 0(x3)

  ret

/**
 * Byte-swaps all eight 32-bit words in w23 into w24.
 *
 * SHA-256 defines message words and state registers in big-endian byte order
 * (FIPS 180-4), whereas OTBN loads 256-bit DMEM words in little-endian byte
 * order. This routine reverses the 4 bytes within each of the eight 32-bit
 * lanes of w23 and wipes w23, w25, and FG0 with fresh randomness from URND
 * before returning so consecutive calls across Share 0 and Share 1 do not
 * induce register or flag-register transition leakage.
 *
 * @param[in]  w8:  Byte-swap lane mask (0x000000ff repeated across 8 lanes).
 * @param[in]  w23: Input 256-bit register containing eight little-endian 32-bit words.
 * @param[out] w24: Output 256-bit register containing eight byte-swapped 32-bit words.
 *
 * Clobbered registers: w23, w24, w25
 * Clobbered flag groups: FG0
 */
bswap32_w23:
  bn.and   w24, w8,  w23
  bn.and   w25, w8,  w23 >> 8
  bn.or    w24, w25, w24 << 8
  bn.and   w25, w8,  w23 >> 16
  bn.or    w24, w25, w24 << 8
  bn.and   w25, w8,  w23 >> 24
  bn.or    w24, w25, w24 << 8
  bn.wsrr  w23, URND
  bn.wsrr  w25, URND
  bn.and   w25, w25, w25
  ret

/**
 * Collects previous MAI result into (w0, w1), immediately starts next MAI
 * addition (w0, w1) + (w2, w3), and returns while MAI runs in background.
 *
 * @param[in]  w2:  Share 0 of second summand.
 * @param[in]  w3:  Share 1 of second summand.
 * @param[in]  x21: MAI_CTRL command word (0x2F for MAI_CTRL_ADD).
 * @param[out] w0:  Share 0 of collected previous MAI result.
 * @param[out] w1:  Share 1 of collected previous MAI result.
 */
sec_add_next:
  csrrs    x20, MAI_STATUS, x0
  andi     x20, x20, 0x1
  bne      x20, x0, sec_add_next
  bn.wsrr  w0, MAI_RES_S0
  bn.xor   w31, w31, w31
  bn.wsrr  w1, MAI_RES_S1
  /* Fall through into sec_add_start */
sec_add_start:
  bn.wsrw  MAI_IN0_S0, w0
  bn.wsrw  MAI_IN1_S0, w2
  bn.wsrw  MAI_IN0_S1, w1
  bn.wsrw  MAI_IN1_S1, w3
  csrrw    x0, MAI_CTRL, x21
  ret

/**
 * Collects result of in-flight MAI addition into (w0, w1).
 *
 * @param[out] w0: Share 0 of 8x32-bit modular addition result.
 * @param[out] w1: Share 1 of 8x32-bit modular addition result.
 */
sec_add_finish:
  csrrs    x20, MAI_STATUS, x0
  andi     x20, x20, 0x1
  bne      x20, x0, sec_add_finish
  bn.wsrr  w0, MAI_RES_S0
  bn.xor   w31, w31, w31
  bn.wsrr  w1, MAI_RES_S1
  ret

/**
 * 1st-order Ishai-Sahai-Wagner (ISW) masked Boolean AND gadget.
 *
 * Computes the bitwise AND of two 256-bit Boolean-shared values x = (x0 ^ x1)
 * and y = (y0 ^ y1) using fresh 256-bit randomness r <- URND:
 *   z0 = (x0 & y0) ^ (r ^ (x0 & y1))
 *   z1 = (x1 & y1) ^ (r ^ (x1 & y0))
 *
 * Note on flag group usage:
 * Every OTBN `bn.and` and `bn.xor` instruction unconditionally updates the
 * selected flag group (FG0 by default, or FG1 when `, FG1` is specified) with
 * the MSB, LSB, and Zero flags of the 256-bit result. Routing Share 0
 * operations to FG0 and Share 1 operations to FG1 ensures Share 1's result
 * flags never overwrite Share 0's result flags in the same flag register,
 * preventing 1st-order flag-register transition leakage.
 *
 * @param[in]  w0: x0, Share 0 of first operand.
 * @param[in]  w1: x1, Share 1 of first operand.
 * @param[in]  w2: y0, Share 0 of second operand.
 * @param[in]  w3: y1, Share 1 of second operand.
 * @param[out] w0: z0, Share 0 of bitwise AND (x & y).
 * @param[out] w1: z1, Share 1 of bitwise AND (x & y).
 *
 * Clobbered registers: w0, w1, w4, w5, w6, w7
 * Clobbered flag groups: FG0, FG1
 */
isw_and:
  bn.wsrr  w7, URND
  bn.and   w4, w0, w2
  bn.xor   w4, w4, w7
  bn.and   w6, w0, w3
  bn.wsrr  w0, URND
  bn.xor   w0, w4, w6
  bn.wsrr  w6, URND
  bn.and   w5, w1, w3, FG1
  bn.xor   w5, w5, w7, FG1
  bn.and   w6, w1, w2, FG1
  bn.wsrr  w1, URND
  bn.xor   w1, w5, w6, FG1
  bn.wsrr  w4, URND
  bn.wsrr  w5, URND
  bn.wsrr  w6, URND
  ret

/**
 * Masked SHA-256 Choose gadget: Ch(e, f, g) = (e & (f ^ g)) ^ g.
 *
 * Evaluates Ch on Boolean-shared state registers using a single call to the
 * 1st-order ISW AND gadget (`isw_and`).
 *
 * @param[in]  w0:  Share 0 of working variable e (in low 32-bit lane).
 * @param[in]  w1:  Share 1 of working variable e (in low 32-bit lane).
 * @param[in]  w23: Share 0 of packed working state (a..h, with f at [95:64], g at [63:32]).
 * @param[in]  w13: Share 1 of packed working state (a..h, with f at [95:64], g at [63:32]).
 * @param[out] w26: Share 0 of Ch(e, f, g) (in low 32-bit lane).
 * @param[out] w16: Share 1 of Ch(e, f, g) (in low 32-bit lane).
 *
 * Clobbered registers: w0..w7, w9, w10, w16, w26, x7
 */
sha256_ch:
  bn.rshi  w9,  w31, w23 >> 32
  bn.xor   w2,  w9,  w9 >> 32
  bn.xor   w31, w31, w31
  bn.rshi  w10, w31, w13 >> 32
  bn.xor   w3,  w10, w10 >> 32, FG1
  addi     x7,  x1,  0
  jal      x1,  isw_and
  bn.xor   w26, w0,  w9
  bn.and   w26, w26, w20
  bn.xor   w31, w31, w31
  bn.xor   w16, w1,  w10, FG1
  bn.and   w16, w16, w20, FG1
  jalr     x0,  x7,  0

/**
 * Masked SHA-256 Majority gadget: Maj(a, b, c) = ((a ^ b) & (a ^ c)) ^ a.
 *
 * Evaluates Maj on Boolean-shared state registers using a single call to the
 * 1st-order ISW AND gadget (`isw_and`). Designed to execute while the MAI
 * accelerator computes Pass 1 of the round additions in the background.
 *
 * @param[in]  w24: Share 0 of working variable a (in low 32-bit lane).
 * @param[in]  w14: Share 1 of working variable a (in low 32-bit lane).
 * @param[in]  w23: Share 0 of packed working state (a..h, with b at [223:192], c at [191:160]).
 * @param[in]  w13: Share 1 of packed working state (a..h, with b at [223:192], c at [191:160]).
 * @param[out] w26: Share 0 of Maj(a, b, c) (in low 32-bit lane).
 * @param[out] w16: Share 1 of Maj(a, b, c) (in low 32-bit lane).
 *
 * Clobbered registers: w0..w7, w16, w26, x7
 */
sha256_maj:
  bn.xor   w0,  w24, w23 >> 192
  bn.xor   w2,  w24, w23 >> 160
  bn.xor   w31, w31, w31
  bn.xor   w1,  w14, w13 >> 192, FG1
  bn.xor   w3,  w14, w13 >> 160, FG1
  addi     x7,  x1,  0
  jal      x1,  isw_and
  bn.xor   w26, w0,  w24
  bn.and   w26, w26, w20
  bn.xor   w31, w31, w31
  bn.xor   w16, w1,  w14, FG1
  bn.and   w16, w16, w20, FG1
  jalr     x0,  x7,  0

/**
 * Computes W[t+16] = sigma1(W[t+14]) + W[t+9] + sigma0(W[t+1]) + W[t]
 * using a 2-pass 2-lane SIMD MAI tree addition.
 */
sha256_expand_w_word:
  addi     x28, x28, -1

  /* sigma1(W[t+14]) on Share 0 -> w27 */
  bn.and   w24, w20, w22 >> 192
  bn.rshi  w25, w24, w31 >> 32
  bn.rshi  w26, w24, w25 >> 17
  bn.rshi  w9,  w24, w25 >> 19
  bn.rshi  w25, w31, w24 >> 10
  bn.xor   w27, w25, w26 >> 224
  bn.xor   w27, w27, w9 >> 224

  /* sigma0(W[t+1]) on Share 0 -> w28 */
  bn.and   w24, w20, w21 >> 32
  bn.rshi  w25, w24, w31 >> 32
  bn.rshi  w26, w24, w25 >> 7
  bn.rshi  w9,  w24, w25 >> 18
  bn.rshi  w25, w31, w24 >> 3
  bn.xor   w28, w25, w26 >> 224
  bn.xor   w28, w28, w9 >> 224
  bn.xor   w31, w31, w31

  /* sigma1(W[t+14]) on Share 1 -> w17 */
  bn.and   w14, w20, w12 >> 192, FG1
  bn.rshi  w15, w14, w31 >> 32
  bn.rshi  w16, w14, w15 >> 17
  bn.rshi  w10, w14, w15 >> 19
  bn.rshi  w15, w31, w14 >> 10
  bn.xor   w17, w15, w16 >> 224, FG1
  bn.xor   w17, w17, w10 >> 224, FG1

  /* sigma0(W[t+1]) on Share 1 -> w18 */
  bn.and   w14, w20, w11 >> 32, FG1
  bn.rshi  w15, w14, w31 >> 32
  bn.rshi  w16, w14, w15 >> 7
  bn.rshi  w10, w14, w15 >> 18
  bn.rshi  w15, w31, w14 >> 3
  bn.xor   w18, w15, w16 >> 224, FG1
  bn.xor   w18, w18, w10 >> 224, FG1

  /* Pack Lane 0 = sigma1(W[t+14]) + W[t+9], Lane 1 = sigma0(W[t+1]) + W[t] */
  bn.or    w0,  w27, w28 << 32
  bn.and   w2,  w20, w22 >> 32
  bn.or    w2,  w2,  w21 << 32
  bn.xor   w31, w31, w31
  bn.or    w1,  w17, w18 << 32, FG1
  bn.and   w3,  w20, w12 >> 32, FG1
  bn.or    w3,  w3,  w11 << 32, FG1
  jal      x1, sec_add_start

  /* Collect 2-lane sum and add Lane 0 + Lane 1 -> W[t+16] in bits 31..0 */
  jal      x1, sec_add_finish
  bn.rshi  w2,  w31, w0 >> 32
  bn.xor   w31, w31, w31
  bn.rshi  w3,  w31, w1 >> 32
  jal      x1, sec_add_start
  jal      x0, sec_add_finish

/**
 * Process a single 512-bit message block using fused sliding-window schedule
 * and 3-pass multi-lane SIMD MAI round updates.
 */
sha256_process_block_masked:
  /* Initialize working variables from hash state */
  bn.mov   w23, w30
  bn.xor   w31, w31, w31
  bn.mov   w13, w29

  la       x18, sha256_K
  li       x28, 48
  li       x22, 19

  /* Main 64-round compression loop (8 outer x 8 inner) */
  loopi    8, 102   /* SCA_TEST_REPLACE: loopi 1, 102 */
    bn.lid   x22, 0(x18++)

    loopi    8, 99
      /* Part A: Share 0 e and S1(e) */
      bn.and   w0,  w20, w23 >> 96
      bn.rshi  w25, w0,  w31 >> 32
      bn.rshi  w26, w0,  w25 >> 6
      bn.rshi  w27, w0,  w25 >> 11
      bn.rshi  w28, w0,  w25 >> 25
      bn.xor   w28, w28, w26
      bn.xor   w28, w28, w27
      bn.xor   w31, w31, w31

      /* Part A: Share 1 e and S1(e) */
      bn.and   w1,  w20, w13 >> 96, FG1
      bn.rshi  w15, w1,  w31 >> 32
      bn.rshi  w16, w1,  w15 >> 6
      bn.rshi  w17, w1,  w15 >> 11
      bn.rshi  w18, w1,  w15 >> 25
      bn.xor   w18, w18, w16, FG1
      bn.xor   w18, w18, w17, FG1

      /* Compute masked Ch(e, f, g) into (w26, w16) and pack (Ch, S1(e)) */
      jal      x1, sha256_ch
      bn.rshi  w26, w26, w28 >> 224
      bn.xor   w31, w31, w31
      bn.rshi  w16, w16, w18 >> 224

      /* Part B: Share 0 S0(a) into w27 */
      bn.and   w24, w20, w23 >> 224
      bn.rshi  w25, w24, w23 >> 2
      bn.rshi  w27, w24, w23 >> 13
      bn.rshi  w28, w24, w23 >> 22
      bn.rshi  w28, w31, w28 >> 224
      bn.xor   w28, w28, w25 >> 224
      bn.xor   w27, w28, w27 >> 224
      bn.xor   w31, w31, w31

      /* Part B: Share 1 S0(a) into w17 */
      bn.and   w14, w20, w13 >> 224, FG1
      bn.rshi  w15, w14, w13 >> 2
      bn.rshi  w17, w14, w13 >> 13
      bn.rshi  w18, w14, w13 >> 22
      bn.rshi  w18, w31, w18 >> 224
      bn.xor   w18, w18, w15 >> 224, FG1
      bn.xor   w17, w18, w17 >> 224, FG1

      /* Pass 1 (4x32 SIMD):
       * Lane 0: h + S1(e)
       * Lane 1: W[t] + Ch(e, f, g)
       * Lane 2: S0(a) + K[t]
       * Lane 3: d + K[t]
       */
      bn.and   w0,  w20, w23
      bn.and   w4,  w20, w21
      bn.or    w0,  w0,  w4 << 32
      bn.or    w0,  w0,  w27 << 64
      bn.and   w4,  w23, w20 << 128
      bn.or    w0,  w0,  w4 >> 32
      bn.and   w4,  w20, w19
      bn.or    w2,  w26, w4 << 64
      bn.or    w2,  w2,  w4 << 96
      bn.wsrr  w4,  URND
      bn.rshi  w4,  w31, w4 >> 192
      bn.xor   w2,  w2,  w4 << 64
      bn.xor   w31, w31, w31

      bn.and   w1,  w20, w13, FG1
      bn.and   w5,  w20, w11, FG1
      bn.or    w1,  w1,  w5 << 32, FG1
      bn.or    w1,  w1,  w17 << 64, FG1
      bn.and   w5,  w13, w20 << 128, FG1
      bn.or    w1,  w1,  w5 >> 32, FG1
      bn.or    w3,  w16, w4 << 64, FG1
      bn.wsrr  w4,  URND
      bn.wsrr  w5,  URND
      jal      x1, sec_add_start

      /* While Pass 1 runs in MAI, compute masked Maj(a, b, c) into (w26, w16) */
      jal      x1, sha256_maj
      jal      x1, sec_add_finish

      /* Pass 2 (4x32 SIMD):
       * Lane 0: (h + S1(e)) + (W[t] + Ch) -> U
       * Lane 2: (S0(a) + K[t]) + Maj      -> T2 + K[t]
       * Lane 3: (d + K[t]) + 0            -> d + K[t]
       */
      bn.and   w2,  w20, w0 >> 32
      bn.or    w2,  w2,  w26 << 64
      bn.xor   w31, w31, w31
      bn.and   w3,  w20, w1 >> 32, FG1
      bn.or    w3,  w3,  w16 << 64, FG1
      jal      x1, sec_add_start

      /* While Pass 2 runs in MAI, shift K and clear d slot [159:128] */
      bn.rshi  w19, w31, w19 >> 32
      bn.and   w24, w23, w20 << 128
      bn.xor   w24, w23, w24
      bn.xor   w31, w31, w31
      bn.and   w14, w13, w20 << 128, FG1
      bn.xor   w14, w13, w14, FG1

      /* Collect Pass 2 and launch Pass 3 (8-lane SIMD state update) */
      jal      x1, sec_add_finish
      bn.and   w25, w0,  w20
      bn.and   w26, w0,  w20 << 64
      bn.rshi  w2,  w26, w31 >> 96
      bn.or    w2,  w2,  w25 << 96
      bn.and   w26, w0,  w20 << 96
      bn.or    w24, w24, w26 << 32
      bn.rshi  w0,  w25, w24 >> 32
      bn.xor   w31, w31, w31

      bn.and   w15, w1,  w20, FG1
      bn.and   w16, w1,  w20 << 64, FG1
      bn.rshi  w3,  w16, w31 >> 96
      bn.or    w3,  w3,  w15 << 96, FG1
      bn.and   w16, w1,  w20 << 96, FG1
      bn.or    w14, w14, w16 << 32, FG1
      bn.rshi  w1,  w15, w14 >> 32
      jal      x1, sec_add_start
      jal      x1, sec_add_finish
      bn.mov   w23, w0
      bn.xor   w31, w31, w31
      bn.mov   w13, w1

      /* Expand W[t+16] (if t < 48) and shift sliding 16-word W window */
      beq      x28, x0, .L_shift_w_only
      jal      x1, sha256_expand_w_word
.L_shift_w_only:
      bn.rshi  w21, w22, w21 >> 32
      bn.rshi  w22, w0,  w22 >> 32
      bn.xor   w31, w31, w31
      bn.rshi  w11, w12, w11 >> 32
      bn.rshi  w12, w1,  w12 >> 32
      /* End of inner loop */

    nop
    /* End of outer loop */

  /* Accumulate working variables into hash state (vectorized 8x32 addition) */
  bn.mov   w0, w30
  bn.mov   w2, w23
  bn.xor   w31, w31, w31
  bn.mov   w1, w29
  bn.mov   w3, w13
  jal      x1, sec_add_start
  jal      x1, sec_add_finish
  bn.mov   w30, w0
  bn.xor   w31, w31, w31
  bn.mov   w29, w1

  ret

.data
.balign 32
bswap32_mask:
  .word 0x000000ff, 0x000000ff, 0x000000ff, 0x000000ff
  .word 0x000000ff, 0x000000ff, 0x000000ff, 0x000000ff

.balign 32
sha256_K:
  .word 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
  .word 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
  .word 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  .word 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
  .word 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
  .word 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
  .word 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  .word 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
