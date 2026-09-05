/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl sha512_masked
.globl bswap64_w0
.globl bswap32_mask
.globl swap32_in_64_mask

.text

/**
 * Masked SHA-512 for OTBN.
 *
 * Processes 1024-bit message blocks using 1st-order Boolean masking:
 * - Rather than expanding the 80-word message schedule into DMEM, maintains a
 *   16-word sliding window directly in eight wide data registers (w21..w24 for
 *   Share 0 and w12..w15 for Share 1), requiring no DMEM scratch space for W.
 * - Hides Masking Accelerator Interface (MAI) latency inside `sec_add64` by
 *   overlapping independent input differences, mask fetches, and register
 *   wiping with MAI execution.
 * - Isolates Share 0 and Share 1 flag updates across OTBN's two flag groups
 *   (Share 0 on default FG0, Share 1 on FG1) and clears the 256-bit BN ALU
 *   datapath with `bn.xor w31, w31, w31` between share operations to prevent
 *   1st-order Hamming-distance transition leakage.
 *
 * @param[in]          x10: Pointer to Share 0 of padded message in DMEM (1024 bits per block)
 * @param[in]          x11: Pointer to Share 1 of padded message in DMEM (1024 bits per block)
 * @param[in]          x30: Number of message blocks to process
 * @param[in]  state_s0   : Share 0 of initial hash state (512 bits: 2 WDRs, efgh at 0, abcd at 32)
 * @param[in]  state_s1   : Share 1 of initial hash state (512 bits: 2 WDRs, efgh at 0, abcd at 32)
 * @param[out] state_s0   : Share 0 of final hash state (512 bits: 2 WDRs, efgh at 0, abcd at 32)
 * @param[out] state_s1   : Share 1 of final hash state (512 bits: 2 WDRs, efgh at 0, abcd at 32)
 */
sha512_masked:
  beq      x30, x0, .L_done_512

  /* Initialize zero register. */
  bn.xor   w31, w31, w31

  /* Create 64-bit mask w20 <= 0x00...00ffffffffffffffff */
  bn.not   w20, w31
  bn.rshi  w20, w31, w20 >> 192

  li       x2, 0
  li       x23, 0x2F

  /* Load byte-swap masks into w8 and w9, and 64-bit carry mask into w19 */
  la       x3, bswap32_mask
  li       x4, 8
  bn.lid   x4, 0(x3)
  la       x3, swap32_in_64_mask
  li       x4, 9
  bn.lid   x4, 0(x3)
  la       x3, carry64_mask
  li       x4, 19
  bn.lid   x4, 0(x3)

  /* Process each 1024-bit message block */
  loop     x30, 18
    /* Load and byte-swap Share 0 (4 WDRs -> w21..w24) */
    loopi    4, 6
      bn.lid   x2, 0(x10++)
      jal      x1, bswap64_w0
      bn.mov   w21, w22
      bn.mov   w22, w23
      bn.mov   w23, w24
      bn.mov   w24, w0
    bn.wsrr  w0, URND

    /* Load and byte-swap Share 1 (4 WDRs -> w12..w15) */
    loopi    4, 6
      bn.lid   x2, 0(x11++)
      jal      x1, bswap64_w0
      bn.mov   w12, w13
      bn.mov   w13, w14
      bn.mov   w14, w15
      bn.mov   w15, w0
    bn.wsrr  w0, URND

    /* Process block with fused sliding-window schedule */
    jal      x1, sha512_process_block_masked
    nop
    /* End of block loop */

.L_done_512:
  ret

/**
 * Byte-swaps all four 64-bit words in w0 in-place.
 *
 * SHA-512 defines 64-bit message words and state registers in big-endian byte
 * order (FIPS 180-4), whereas OTBN loads 256-bit DMEM words in little-endian
 * byte order. This routine reverses the 8 bytes within each of the four 64-bit
 * lanes of w0 and wipes temporary registers w4..w7 and FG0 with URND before
 * returning so consecutive calls across Share 0 and Share 1 do not leak.
 *
 * @param[in]  w0: Input 256-bit register containing four little-endian 64-bit words.
 * @param[in]  w8: 32-bit byte-swap mask (0x000000ff repeated across 8 lanes).
 * @param[in]  w9: 64-bit half-word swap mask (0x00000000ffffffff repeated across 4 lanes).
 * @param[out] w0: Output 256-bit register containing four byte-swapped 64-bit words.
 *
 * Clobbered registers: w0, w4, w5, w6, w7
 * Clobbered flag groups: FG0
 */
bswap64_w0:
  bn.and   w4, w8, w0
  bn.and   w5, w8, w0 >> 8
  bn.and   w6, w8, w0 >> 16
  bn.and   w7, w8, w0 >> 24
  bn.or    w0, w5, w4 << 8
  bn.or    w0, w6, w0 << 8
  bn.or    w0, w7, w0 << 8
  bn.and   w4, w9, w0
  bn.and   w5, w9, w0 >> 32
  bn.or    w0, w5, w4 << 32
  bn.wsrr  w4, URND
  bn.wsrr  w5, URND
  bn.wsrr  w6, URND
  bn.wsrr  w7, URND
  bn.and   w7, w7, w7
  ret

/**
 * Secure 4x64-bit addition modulo 2^64 using the 32-bit MAI accelerator.
 *
 * Since MAI computes 8x32-bit Boolean-shared modular additions (with no carry
 * propagation from even 32-bit lanes [31:0] into odd 32-bit lanes [63:32]),
 * this gadget performs 4x64-bit addition in two MAI passes:
 *   1. First MAI pass computes the 8x32-bit sum S = X + Y (mod 2^32 per lane).
 *   2. The Boolean-shared carry out of each even 32-bit lane (bit 31 of X, Y, S)
 *      is extracted using the identity:
 *        carry = Majority(X[31], Y[31], ~S[31]) = X[31] ^ ((X[31] ^ Y[31]) & (Y[31] ^ S[31]))
 *      evaluated via a 1st-order masked AND with fresh randomness from URND,
 *      shifted to bit 0 of the adjacent odd 32-bit lane, and masked with w19.
 *   3. Second MAI pass adds the masked carry into the odd 32-bit lanes.
 *
 * @param[in]  w0:  Share 0 of first 4x64-bit summand X.
 * @param[in]  w1:  Share 1 of first 4x64-bit summand X.
 * @param[in]  w2:  Share 0 of second 4x64-bit summand Y.
 * @param[in]  w3:  Share 1 of second 4x64-bit summand Y.
 * @param[in]  w19: Carry lane mask (0x0000000100000000 repeated across 4 lanes).
 * @param[in]  x23: MAI_CTRL command word (0x2F for MAI_CTRL_ADD).
 * @param[out] w0:  Share 0 of 4x64-bit modular sum (X + Y) mod 2^64.
 * @param[out] w1:  Share 1 of 4x64-bit modular sum (X + Y) mod 2^64.
 *
 * Clobbered registers: w0..w7, w10, w11, x20
 * Clobbered flag groups: FG0, FG1
 */
sec_add64:
  bn.wsrw  MAI_IN0_S0, w0
  bn.wsrw  MAI_IN1_S0, w2
  bn.wsrw  MAI_IN0_S1, w1
  bn.wsrw  MAI_IN1_S1, w3
  csrrw    x0, MAI_CTRL, x23

  /* While 1st MAI addition runs, compute X ^ Y differences and fetch masks */
  bn.xor   w4, w0, w2
  bn.xor   w31, w31, w31
  bn.xor   w5, w1, w3, FG1
  bn.wsrr  w6, URND
  bn.wsrr  w7, URND

.L_mai_poll_1:
  csrrs    x20, MAI_STATUS, x0
  andi     x20, x20, 0x1
  bne      x20, x0, .L_mai_poll_1

  bn.wsrr  w10, MAI_RES_S0
  bn.xor   w10, w10, w6
  bn.xor   w31, w31, w31
  bn.wsrr  w11, MAI_RES_S1
  bn.xor   w11, w11, w6, FG1
  bn.xor   w31, w31, w31

  /* Compute Y ^ S differences */
  bn.xor   w6, w2, w10
  bn.wsrr  w2, URND
  bn.xor   w31, w31, w31
  bn.xor   w2, w3, w11, FG1
  bn.wsrr  w3, URND
  bn.xor   w31, w31, w31

  /* Share 0 carry accumulation into w0 */
  bn.xor   w0, w0, w7
  bn.and   w3, w4, w6
  bn.xor   w0, w0, w3
  bn.wsrr  w3, URND
  bn.and   w3, w4, w2
  bn.xor   w0, w0, w3
  bn.wsrr  w3, URND
  bn.xor   w31, w31, w31

  /* Share 1 carry accumulation into w1 (using FG1) */
  bn.xor   w1, w1, w7, FG1
  bn.and   w3, w5, w2, FG1
  bn.xor   w1, w1, w3, FG1
  bn.wsrr  w3, URND
  bn.and   w3, w5, w6, FG1
  bn.xor   w1, w1, w3, FG1
  bn.wsrr  w3, URND
  bn.wsrr  w2, URND
  bn.xor   w31, w31, w31

  /* Shift carry into bit 0 of each odd 32-bit lane */
  bn.rshi  w2, w0, w0 >> 255
  bn.and   w2, w19, w2
  bn.xor   w31, w31, w31
  bn.rshi  w3, w1, w1 >> 255
  bn.and   w3, w19, w3, FG1

  bn.wsrw  MAI_IN0_S0, w10
  bn.wsrw  MAI_IN1_S0, w2
  bn.wsrw  MAI_IN0_S1, w11
  bn.wsrw  MAI_IN1_S1, w3
  csrrw    x0, MAI_CTRL, x23

  /* While 2nd MAI addition runs, wipe temporaries and fetch output mask */
  bn.wsrr  w2,  URND
  bn.wsrr  w3,  URND
  bn.wsrr  w4,  URND
  bn.wsrr  w5,  URND
  bn.wsrr  w6,  URND
  bn.wsrr  w7,  URND
  bn.wsrr  w10, URND
  bn.wsrr  w11, URND

.L_mai_poll_2:
  csrrs    x20, MAI_STATUS, x0
  andi     x20, x20, 0x1
  bne      x20, x0, .L_mai_poll_2

  bn.wsrr  w0, MAI_RES_S0
  bn.xor   w0, w0, w4
  bn.xor   w31, w31, w31
  bn.wsrr  w1, MAI_RES_S1
  bn.xor   w1, w1, w4, FG1
  bn.wsrr  w4, URND
  ret

/**
 * 1st-order Ishai-Sahai-Wagner (ISW) masked Boolean AND gadget.
 *
 * Computes the bitwise AND of two 256-bit Boolean-shared values x = (x0 ^ x1)
 * and y = (y0 ^ y1) using fresh 256-bit randomness r <- URND:
 *   z0 = (x0 & y0) ^ (r ^ (x0 & y1))
 *   z1 = (x1 & y1) ^ (r ^ (x1 & y0))
 *
 * Share 0 operations target flag group FG0 (default) while Share 1 operations
 * target FG1 so Share 1's status flags never overwrite Share 0's status flags.
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
 * Masked SHA-512 Choose gadget: Ch(e, f, g) = (e & (f ^ g)) ^ g.
 *
 * @param[in]  w27: Share 0 of working variable e (low 64 bits).
 * @param[in]  w10: Share 1 of working variable e (low 64 bits).
 * @param[in]  w25: Share 0 of working state (e, f, g, h).
 * @param[in]  w16: Share 1 of working state (e, f, g, h).
 * @param[out] w27: Share 0 of Ch(e, f, g) (low 64 bits).
 * @param[out] w30: Share 1 of Ch(e, f, g) (low 64 bits).
 *
 * Clobbered registers: w0..w7, w27, w29, w30, x7
 */
sha512_ch:
  bn.and   w2,  w20, w25 >> 128
  bn.and   w29, w20, w25 >> 64
  bn.xor   w2,  w2,  w29
  bn.mov   w0,  w27
  bn.xor   w31, w31, w31
  bn.and   w3,  w20, w16 >> 128, FG1
  bn.and   w30, w20, w16 >> 64, FG1
  bn.xor   w3,  w3,  w30, FG1
  bn.mov   w1,  w10
  addi     x7,  x1,  0
  jal      x1,  isw_and
  bn.and   w0,  w0,  w20
  bn.xor   w27, w0,  w29
  bn.xor   w31, w31, w31
  bn.and   w1,  w1,  w20, FG1
  bn.xor   w30, w1,  w30, FG1
  jalr     x0,  x7,  0

/**
 * Masked SHA-512 Majority gadget: Maj(a, b, c) = ((a ^ b) & (a ^ c)) ^ a.
 *
 * @param[in]  w28: Share 0 of working variable a (low 64 bits).
 * @param[in]  w10: Share 1 of working variable a (low 64 bits).
 * @param[in]  w26: Share 0 of working state (a, b, c, d).
 * @param[in]  w17: Share 1 of working state (a, b, c, d).
 * @param[out] w0:  Share 0 of Maj(a, b, c) (low 64 bits).
 * @param[out] w1:  Share 1 of Maj(a, b, c) (low 64 bits).
 *
 * Clobbered registers: w0..w7, x7
 */
sha512_maj:
  bn.and   w2,  w20, w26 >> 128
  bn.and   w4,  w20, w26 >> 64
  bn.xor   w0,  w28, w2
  bn.xor   w2,  w28, w4
  bn.wsrr  w4,  URND
  bn.xor   w31, w31, w31
  bn.and   w3,  w20, w17 >> 128, FG1
  bn.and   w4,  w20, w17 >> 64, FG1
  bn.xor   w1,  w10, w3, FG1
  bn.xor   w3,  w10, w4, FG1
  bn.wsrr  w4,  URND
  addi     x7,  x1,  0
  jal      x1,  isw_and
  bn.and   w0,  w0,  w20
  bn.xor   w0,  w0,  w28
  bn.xor   w31, w31, w31
  bn.and   w1,  w1,  w20, FG1
  bn.xor   w1,  w1,  w10, FG1
  jalr     x0,  x7,  0

/**
 * Computes W[t+16] = sigma1(W[t+14]) + W[t+9] + sigma0(W[t+1]) + W[t]
 * from the 16-word sliding window in (w21..w24) and (w12..w15).
 * Returns W[t+16] in (w0, w1). Preserves state (w25, w26, w16, w17) and K (w18).
 */
sha512_expand_w_word:
  /* sigma1(W[t+14]) on Share 0 -> w27 */
  bn.and   w4,  w20, w24 >> 128
  bn.rshi  w5,  w4,  w31 >> 64
  bn.rshi  w27, w4,  w5 >> 19
  bn.rshi  w6,  w4,  w5 >> 61
  bn.rshi  w5,  w31, w4 >> 6
  bn.xor   w27, w5,  w27 >> 192
  bn.xor   w27, w27, w6 >> 192

  /* sigma0(W[t+1]) on Share 0 -> w28 */
  bn.and   w4,  w20, w21 >> 64
  bn.rshi  w5,  w4,  w31 >> 64
  bn.rshi  w28, w4,  w5 >> 1
  bn.rshi  w6,  w4,  w5 >> 8
  bn.rshi  w5,  w31, w4 >> 7
  bn.xor   w28, w5,  w28 >> 192
  bn.xor   w28, w28, w6 >> 192

  bn.wsrr  w4,  URND
  bn.wsrr  w5,  URND
  bn.wsrr  w6,  URND

  /* sigma1(W[t+14]) on Share 1 -> w29 */
  bn.and   w4,  w20, w15 >> 128, FG1
  bn.rshi  w5,  w4,  w31 >> 64
  bn.rshi  w29, w4,  w5 >> 19
  bn.rshi  w6,  w4,  w5 >> 61
  bn.rshi  w5,  w31, w4 >> 6
  bn.xor   w29, w5,  w29 >> 192, FG1
  bn.xor   w29, w29, w6 >> 192, FG1

  /* sigma0(W[t+1]) on Share 1 -> w30 */
  bn.and   w4,  w20, w12 >> 64, FG1
  bn.rshi  w5,  w4,  w31 >> 64
  bn.rshi  w30, w4,  w5 >> 1
  bn.rshi  w6,  w4,  w5 >> 8
  bn.rshi  w5,  w31, w4 >> 7
  bn.xor   w30, w5,  w30 >> 192, FG1
  bn.xor   w30, w30, w6 >> 192, FG1

  bn.wsrr  w4,  URND
  bn.wsrr  w5,  URND
  bn.wsrr  w6,  URND

  /* Pack Lane 0 = W[t] + sigma1(W[t+14]), Lane 1 = sigma0(W[t+1]) + W[t+9] */
  bn.and   w0, w20, w21
  bn.or    w0, w0,  w28 << 64
  bn.and   w2, w20, w23 >> 64
  bn.or    w2, w27, w2 << 64
  bn.xor   w31, w31, w31
  bn.and   w1, w20, w12, FG1
  bn.or    w1, w1,  w30 << 64, FG1
  bn.and   w3, w20, w14 >> 64, FG1
  bn.or    w3, w29, w3 << 64, FG1
  jal      x1, sec_add64

  /* Add Lane 0 + Lane 1 -> W[t+16] in bits 63..0 */
  bn.rshi  w2, w31, w0 >> 64
  bn.xor   w31, w31, w31
  bn.rshi  w3, w31, w1 >> 64
  jal      x1, sec_add64
  ret

/**
 * Process a single 1024-bit message block using fused sliding-window schedule.
 */
sha512_process_block_masked:
  /* Initialize working variables from hash state in DMEM:
   * Share 0: w25 = efgh_s0, w26 = abcd_s0
   * Share 1: w16 = efgh_s1, w17 = abcd_s1
   */
  la       x3, state_s0
  li       x4, 25
  bn.lid   x4, 0(x3)
  li       x4, 26
  bn.lid   x4, 32(x3)
  la       x3, state_s1
  li       x4, 16
  bn.lid   x4, 0(x3)
  li       x4, 17
  bn.lid   x4, 32(x3)

  la       x18, sha512_K
  li       x22, 18
  li       x28, 64

  /* Main 80-round compression loop (20 outer iterations x 4 inner rounds) */
  loopi    20, 99   /* SCA_TEST_REPLACE: loopi 1, 99 */
    bn.lid   x22, 0(x18++)

    loopi    4, 96
      /* Part A: Share 0 e and S1(e) */
      bn.and   w27, w20, w25 >> 192
      bn.rshi  w4,  w27, w25 >> 14
      bn.rshi  w5,  w27, w25 >> 18
      bn.rshi  w28, w27, w25 >> 41
      bn.xor   w28, w28, w4
      bn.xor   w28, w28, w5
      bn.wsrr  w4,  URND
      bn.wsrr  w5,  URND

      /* Part A: Share 1 e and S1(e) */
      bn.and   w10, w20, w16 >> 192, FG1
      bn.rshi  w4,  w10, w16 >> 14
      bn.rshi  w5,  w10, w16 >> 18
      bn.rshi  w11, w10, w16 >> 41
      bn.xor   w11, w11, w4, FG1
      bn.xor   w11, w11, w5, FG1
      bn.wsrr  w4,  URND
      bn.wsrr  w5,  URND

      /* Compute masked Ch(e, f, g) into (w27, w30) and pack (Ch, S1(e)) */
      jal      x1, sha512_ch
      bn.rshi  w27, w27, w28 >> 192
      bn.xor   w31, w31, w31
      bn.rshi  w30, w30, w11 >> 192

      /* Part B: Share 0 a and S0(a) */
      bn.and   w28, w20, w26 >> 192
      bn.rshi  w4,  w28, w26 >> 28
      bn.rshi  w5,  w28, w26 >> 34
      bn.rshi  w29, w28, w26 >> 39
      bn.xor   w29, w29, w4
      bn.xor   w29, w29, w5
      bn.wsrr  w4,  URND
      bn.wsrr  w5,  URND

      /* Part B: Share 1 a and S0(a) */
      bn.and   w10, w20, w17 >> 192, FG1
      bn.rshi  w4,  w10, w17 >> 28
      bn.rshi  w5,  w10, w17 >> 34
      bn.rshi  w11, w10, w17 >> 39
      bn.xor   w11, w11, w4, FG1
      bn.xor   w11, w11, w5, FG1
      bn.wsrr  w4,  URND
      bn.wsrr  w5,  URND

      /* Compute masked Maj(a, b, c) into (w0, w1) */
      jal      x1, sha512_maj

      /* Pass 1 (4x64 SIMD):
       * Lane 0: h + S1(e)
       * Lane 1: W[t] + Ch(e, f, g)
       * Lane 2: d + K[t]
       * Lane 3: Maj(a, b, c) + S0(a) = T2
       */
      bn.rshi  w0,  w0,  w31 >> 64
      bn.and   w4,  w20, w25
      bn.or    w0,  w0,  w4
      bn.and   w4,  w20, w21
      bn.or    w0,  w0,  w4 << 64
      bn.and   w4,  w20, w26
      bn.or    w0,  w0,  w4 << 128
      bn.and   w4,  w20, w18
      bn.or    w2,  w27, w4 << 128
      bn.and   w4,  w29, w20 << 192
      bn.or    w2,  w2,  w4
      bn.wsrr  w4,  URND
      bn.xor   w31, w31, w31

      bn.rshi  w1,  w1,  w31 >> 64
      bn.and   w4,  w20, w16, FG1
      bn.or    w1,  w1,  w4, FG1
      bn.and   w4,  w20, w12, FG1
      bn.or    w1,  w1,  w4 << 64, FG1
      bn.and   w4,  w20, w17, FG1
      bn.or    w1,  w1,  w4 << 128, FG1
      bn.and   w4,  w11, w20 << 192, FG1
      bn.or    w3,  w30, w4, FG1
      bn.wsrr  w4,  URND
      jal      x1, sec_add64

      /* Pass 2 (4x64 SIMD):
       * Lane 0: (h + S1(e)) + (W[t] + Ch) -> U
       * Lane 2: (d + K[t]) + 0            -> d + K[t]
       * Lane 3: T2 + K[t]                 -> T2 + K[t]
       */
      bn.and   w2,  w20, w0 >> 64
      bn.or    w2,  w2,  w18 << 192
      bn.xor   w31, w31, w31
      bn.and   w3,  w20, w1 >> 64, FG1
      jal      x1, sec_add64

      /* Pass 3 (4x64 SIMD):
       * Lane 0: U + (d + K[t])  -> new_e
       * Lane 1: U + (T2 + K[t]) -> new_a
       */
      bn.rshi  w2,  w31, w0 >> 128
      bn.and   w0,  w0,  w20
      bn.or    w0,  w0,  w0 << 64
      bn.xor   w31, w31, w31
      bn.rshi  w3,  w31, w1 >> 128
      bn.and   w1,  w1,  w20, FG1
      bn.or    w1,  w1,  w1 << 64, FG1
      jal      x1, sec_add64

      /* Shift working state and K on Share 0 */
      bn.rshi  w25, w0,  w25 >> 64
      bn.rshi  w0,  w31, w0 >> 64
      bn.rshi  w26, w0,  w26 >> 64
      bn.rshi  w18, w31, w18 >> 64
      bn.xor   w31, w31, w31

      /* Shift working state on Share 1 */
      bn.rshi  w16, w1,  w16 >> 64
      bn.rshi  w1,  w31, w1 >> 64
      bn.rshi  w17, w1,  w17 >> 64

      /* Expand W[t+16] (if t < 64) and shift 16-word W sliding window */
      beq      x28, x0, .L_shift_w_only
      addi     x28, x28, -1
      jal      x1, sha512_expand_w_word
.L_shift_w_only:
      bn.and   w0,  w0,  w20
      bn.rshi  w21, w22, w21 >> 64
      bn.rshi  w22, w23, w22 >> 64
      bn.rshi  w23, w24, w23 >> 64
      bn.rshi  w24, w0,  w24 >> 64
      bn.xor   w31, w31, w31
      bn.and   w1,  w1,  w20, FG1
      bn.rshi  w12, w13, w12 >> 64
      bn.rshi  w13, w14, w13 >> 64
      bn.rshi  w14, w15, w14 >> 64
      bn.rshi  w15, w1,  w15 >> 64
      /* End of inner loop */

    nop
    /* End of outer loop */

  /* Accumulate working variables into hash state in DMEM */
  la       x16, state_s0
  li       x2, 30
  bn.lid   x2, 0(x16)
  li       x2, 28
  bn.lid   x2, 32(x16)
  la       x16, state_s1
  li       x2, 27
  bn.lid   x2, 0(x16)
  li       x2, 29
  bn.lid   x2, 32(x16)

  /* Add efgh: (w30, w27) + (w25, w16) */
  bn.mov   w0, w30
  bn.mov   w2, w25
  bn.xor   w31, w31, w31
  bn.mov   w1, w27
  bn.mov   w3, w16
  jal      x1, sec_add64
  la       x16, state_s0
  li       x2, 0
  bn.sid   x2, 0(x16)
  la       x16, state_s1
  li       x2, 1
  bn.sid   x2, 0(x16)

  /* Add abcd: (w28, w29) + (w26, w17) */
  bn.mov   w0, w28
  bn.mov   w2, w26
  bn.xor   w31, w31, w31
  bn.mov   w1, w29
  bn.mov   w3, w17
  jal      x1, sec_add64
  la       x16, state_s0
  li       x2, 0
  bn.sid   x2, 32(x16)
  la       x16, state_s1
  li       x2, 1
  bn.sid   x2, 32(x16)
  li       x2, 0

  ret

.data
.balign 32
bswap32_mask:
  .word 0x000000ff, 0x000000ff, 0x000000ff, 0x000000ff
  .word 0x000000ff, 0x000000ff, 0x000000ff, 0x000000ff

.balign 32
swap32_in_64_mask:
  .dword 0x00000000ffffffff, 0x00000000ffffffff, 0x00000000ffffffff, 0x00000000ffffffff

.balign 32
carry64_mask:
  .dword 0x0000000100000000, 0x0000000100000000, 0x0000000100000000, 0x0000000100000000

.balign 32
sha512_K:
  .dword 0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc
  .dword 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118
  .dword 0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2
  .dword 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694
  .dword 0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65
  .dword 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5
  .dword 0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4
  .dword 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70
  .dword 0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df
  .dword 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b
  .dword 0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30
  .dword 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8
  .dword 0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8
  .dword 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3
  .dword 0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec
  .dword 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b
  .dword 0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178
  .dword 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b
  .dword 0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c
  .dword 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817
