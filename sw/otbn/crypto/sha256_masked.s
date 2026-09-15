/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

.globl sha256_masked

.text

/**
 * Masked SHA-256 for OTBN.
 *
 * Cautionary note: this masking has not yet been tested!
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
  /* Initialize zero register. */
  bn.xor   w31, w31, w31

  /* Create 32-bit mask w20 <= 0x00...00ffffffff */
  bn.not   w20, w31
  bn.rshi  w20, w31, w20 >> 224

  /* Set MOD to 0 (modulo 2^32 for 32-bit MAI additions) */
  bn.wsrw  MOD, w31

  /* Initialize constants for indirect register addressing */
  li       x21, 21
  li       x22, 22
  li       x23, 23
  li       x5,  11
  li       x6,  12

  /* Load initial state shares */
  la       x3, state_s0
  li       x2, 30
  bn.lid   x2, 0(x3)

  la       x3, state_s1
  li       x2, 29
  bn.lid   x2, 0(x3)

  /* Load byte-swap mask into w8 (preserved across all calls) */
  la       x2, bswap32_mask
  li       x3, 8
  bn.lid   x3, 0(x2)

  /* Process each 512-bit message block */
  loop     x30, 38
    /* Load and byte-swap Share 0 lower 256 bits -> w21 */
    bn.lid   x23, 0(x10++)
    bn.and   w24, w8,  w23
    bn.and   w25, w8,  w23 >> 8
    bn.and   w26, w8,  w23 >> 16
    bn.and   w3,  w8,  w23 >> 24
    bn.or    w23, w25, w24 << 8
    bn.or    w23, w26, w23 << 8
    bn.or    w23, w3,  w23 << 8
    bn.movr  x21, x23

    /* Load and byte-swap Share 1 lower 256 bits -> w11 (via x5) */
    bn.lid   x23, 0(x11++)
    bn.and   w24, w8,  w23
    bn.and   w25, w8,  w23 >> 8
    bn.and   w26, w8,  w23 >> 16
    bn.and   w3,  w8,  w23 >> 24
    bn.or    w23, w25, w24 << 8
    bn.or    w23, w26, w23 << 8
    bn.or    w23, w3,  w23 << 8
    bn.movr  x5,  x23

    /* Load and byte-swap Share 0 upper 256 bits -> w22 */
    bn.lid   x23, 0(x10++)
    bn.and   w24, w8,  w23
    bn.and   w25, w8,  w23 >> 8
    bn.and   w26, w8,  w23 >> 16
    bn.and   w3,  w8,  w23 >> 24
    bn.or    w23, w25, w24 << 8
    bn.or    w23, w26, w23 << 8
    bn.or    w23, w3,  w23 << 8
    bn.movr  x22, x23

    /* Load and byte-swap Share 1 upper 256 bits -> w12 (via x6) */
    bn.lid   x23, 0(x11++)
    bn.and   w24, w8,  w23
    bn.and   w25, w8,  w23 >> 8
    bn.and   w26, w8,  w23 >> 16
    bn.and   w3,  w8,  w23 >> 24
    bn.or    w23, w25, w24 << 8
    bn.or    w23, w26, w23 << 8
    bn.or    w23, w3,  w23 << 8
    bn.movr  x6,  x23

    /* Process block */
    jal      x1, sha256_process_block_masked
    nop
    /* End of loop */

  /* Write back final state shares */
  la       x3, state_s0
  li       x2, 30
  bn.sid   x2, 0(x3)

  la       x3, state_s1
  li       x2, 29
  bn.sid   x2, 0(x3)

  ret

/**
 * Secure 8x32 addition modulo 2^32 using MAI accelerator.
 * Computes (w0, w1) = (w0, w1) + (w2, w3) mod 2^32 across 8 lanes.
 */
sec_add:
  bn.wsrw  MAI_IN0_S0, w0
  bn.wsrw  MAI_IN1_S0, w2
  addi     x20, x0, 0x2F
  bn.wsrw  MAI_IN0_S1, w1
  bn.wsrw  MAI_IN1_S1, w3
  csrrw    x0, MAI_CTRL, x20
.L_mai_poll:
  csrrs    x20, MAI_STATUS, x0
  andi     x20, x20, 0x1
  bne      x20, x0, .L_mai_poll
  bn.wsrr  w0, MAI_RES_S0
  bn.xor   w31, w31, w31
  bn.wsrr  w1, MAI_RES_S1
  ret

/**
 * 1st-order ISW Boolean AND gadget.
 * Computes (w0, w1) = (w0, w1) & (w2, w3).
 * Uses w4, w5, w6, w7 as temporaries.
 */
isw_and:
  bn.wsrr  w7, URND
  bn.and   w4, w0, w2
  bn.xor   w4, w4, w7
  bn.and   w5, w1, w3
  bn.xor   w5, w5, w7
  bn.and   w6, w0, w3
  bn.xor   w5, w5, w6
  bn.and   w6, w1, w2
  bn.xor   w1, w5, w6
  bn.mov   w0, w4
  ret

/**
 * Process a single 512-bit message block.
 */
sha256_process_block_masked:
  /* Store initial 16 words of W schedule */
  la       x11, sha256_W_s0
  la       x12, sha256_W_s1
  bn.sid   x21, 0(x11++)
  bn.sid   x5,  0(x12++)
  bn.sid   x22, 0(x11++)
  bn.sid   x6,  0(x12++)

  /* Expand message schedule: 3 passes of 16 words */
  loopi    3, 54
    loopi    16, 49
      /* sigma1(W[t-2]) on Share 0 */
      bn.and   w23, w20, w22 >> 192
      bn.rshi  w24, w23, w31 >> 32
      bn.rshi  w25, w23, w24 >> 17
      bn.rshi  w26, w23, w24 >> 19
      bn.rshi  w24, w31, w23 >> 10
      bn.xor   w27, w24, w25 >> 224
      bn.xor   w27, w27, w26 >> 224
      bn.and   w27, w27, w20

      /* sigma1(W[t-2]) on Share 1 */
      bn.and   w13, w20, w12 >> 192
      bn.rshi  w14, w13, w31 >> 32
      bn.rshi  w15, w13, w14 >> 17
      bn.rshi  w16, w13, w14 >> 19
      bn.rshi  w14, w31, w13 >> 10
      bn.xor   w17, w14, w15 >> 224
      bn.xor   w17, w17, w16 >> 224
      bn.and   w17, w17, w20

      /* sigma0(W[t-15]) on Share 0 */
      bn.and   w23, w20, w21 >> 32
      bn.rshi  w24, w23, w31 >> 32
      bn.rshi  w25, w23, w24 >> 7
      bn.rshi  w26, w23, w24 >> 18
      bn.rshi  w24, w31, w23 >> 3
      bn.xor   w28, w24, w25 >> 224
      bn.xor   w28, w28, w26 >> 224
      bn.and   w28, w28, w20

      /* sigma0(W[t-15]) on Share 1 */
      bn.and   w13, w20, w11 >> 32
      bn.rshi  w14, w13, w31 >> 32
      bn.rshi  w15, w13, w14 >> 7
      bn.rshi  w16, w13, w14 >> 18
      bn.rshi  w14, w31, w13 >> 3
      bn.xor   w18, w14, w15 >> 224
      bn.xor   w18, w18, w16 >> 224
      bn.and   w18, w18, w20

      /* W[t] = sigma1 + W[t-7] + sigma0 + W[t-16] */
      bn.mov   w0, w27
      bn.mov   w1, w17
      bn.and   w2, w20, w22 >> 32
      bn.and   w3, w20, w12 >> 32
      jal      x1, sec_add

      bn.mov   w2, w28
      bn.mov   w3, w18
      jal      x1, sec_add

      bn.and   w2, w20, w21
      bn.and   w3, w20, w11
      jal      x1, sec_add

      bn.and   w0, w0, w20
      bn.and   w1, w1, w20

      /* Shift W window */
      bn.rshi  w21, w22, w21 >> 32
      bn.rshi  w11, w12, w11 >> 32
      bn.rshi  w22, w0,  w22 >> 32
      bn.rshi  w12, w1,  w12 >> 32
      /* End of loop */

    bn.sid   x21, 0(x11++)
    bn.sid   x5,  0(x12++)
    bn.sid   x22, 0(x11++)
    bn.sid   x6,  0(x12++)
    /* End of loop */

  /* Initialize working variables from hash state */
  bn.mov   w23, w30
  bn.mov   w13, w29

  la       x11, sha256_W_s0
  la       x12, sha256_W_s1
  la       x13, sha256_K

  /* Main 64-round compression loop */
  loopi    8, 107
    bn.lid   x21, 0(x11++)
    bn.lid   x5,  0(x12++)
    bn.lid   x22, 0(x13++)

    loopi    8, 102
      /* Extract e shares */
      bn.and   w24, w20, w23 >> 96
      bn.and   w14, w20, w13 >> 96
      bn.rshi  w25, w24, w31 >> 32
      bn.rshi  w15, w14, w31 >> 32

      /* S1(e) */
      bn.rshi  w26, w24, w25 >> 6
      bn.rshi  w16, w14, w15 >> 6
      bn.rshi  w27, w24, w25 >> 11
      bn.rshi  w17, w14, w15 >> 11
      bn.rshi  w28, w24, w25 >> 25
      bn.rshi  w18, w14, w15 >> 25
      bn.xor   w28, w28, w26
      bn.xor   w18, w18, w16
      bn.xor   w28, w28, w27
      bn.xor   w18, w18, w17

      /* Ch(e, f, g) = e & (f ^ g) ^ g */
      bn.and   w2, w20, w23 >> 64
      bn.and   w3, w20, w13 >> 64
      bn.and   w9, w20, w23 >> 32
      bn.and   w10, w20, w13 >> 32
      bn.xor   w2, w2, w9
      bn.xor   w3, w3, w10

      bn.mov   w0, w24
      bn.mov   w1, w14
      jal      x1, isw_and
      bn.and   w0, w0, w20
      bn.and   w1, w1, w20
      bn.xor   w26, w0, w9
      bn.xor   w16, w1, w10

      /* T1 = h + S1(e) + Ch + K[t] + W[t] */
      bn.and   w0, w20, w23
      bn.and   w1, w20, w13
      bn.rshi  w2, w31, w28 >> 224
      bn.rshi  w3, w31, w18 >> 224
      bn.and   w2, w2, w20
      bn.and   w3, w3, w20
      jal      x1, sec_add

      bn.mov   w2, w26
      bn.mov   w3, w16
      jal      x1, sec_add

      bn.and   w2, w20, w22
      bn.mov   w3, w31
      jal      x1, sec_add

      bn.and   w2, w20, w21
      bn.and   w3, w20, w11
      jal      x1, sec_add

      bn.and   w25, w0, w20
      bn.and   w15, w1, w20

      /* Extract a shares */
      bn.and   w24, w20, w23 >> 224
      bn.and   w14, w20, w13 >> 224

      /* S0(a) */
      bn.rshi  w26, w24, w23 >> 2
      bn.rshi  w16, w14, w13 >> 2
      bn.rshi  w27, w24, w23 >> 13
      bn.rshi  w17, w14, w13 >> 13
      bn.rshi  w28, w24, w23 >> 22
      bn.rshi  w18, w14, w13 >> 22
      bn.xor   w28, w28, w26
      bn.xor   w18, w18, w16
      bn.xor   w28, w28, w27
      bn.xor   w18, w18, w17

      /* Maj(a, b, c) = (a ^ b) & (a ^ c) ^ a */
      bn.and   w2, w20, w23 >> 192
      bn.and   w3, w20, w13 >> 192
      bn.and   w4, w20, w23 >> 160
      bn.and   w5, w20, w13 >> 160
      bn.xor   w0, w24, w2
      bn.xor   w1, w14, w3
      bn.xor   w2, w24, w4
      bn.xor   w3, w14, w5
      jal      x1, isw_and
      bn.and   w0, w0, w20
      bn.and   w1, w1, w20
      bn.xor   w26, w0, w24
      bn.xor   w16, w1, w14

      /* T2 = S0(a) + Maj */
      bn.mov   w0, w26
      bn.mov   w1, w16
      bn.rshi  w2, w31, w28 >> 224
      bn.rshi  w3, w31, w18 >> 224
      bn.and   w2, w2, w20
      bn.and   w3, w3, w20
      jal      x1, sec_add

      /* T1 + T2 */
      bn.mov   w2, w25
      bn.mov   w3, w15
      jal      x1, sec_add
      bn.and   w26, w0, w20
      bn.and   w16, w1, w20

      /* Shift working variables */
      bn.rshi  w23, w26, w23 >> 32
      bn.rshi  w13, w16, w13 >> 32

      /* Update e = d + T1 */
      bn.and   w24, w23, w20 << 96
      bn.and   w14, w13, w20 << 96
      bn.xor   w23, w23, w24
      bn.xor   w13, w13, w14

      bn.rshi  w0, w31, w24 >> 96
      bn.rshi  w1, w31, w14 >> 96
      bn.and   w0, w0, w20
      bn.and   w1, w1, w20
      bn.mov   w2, w25
      bn.mov   w3, w15
      jal      x1, sec_add

      bn.and   w0, w0, w20
      bn.and   w1, w1, w20
      bn.or    w23, w23, w0 << 96
      bn.or    w13, w13, w1 << 96

      /* Shift W and K */
      bn.rshi  w21, w31, w21 >> 32
      bn.rshi  w11, w31, w11 >> 32
      bn.rshi  w22, w31, w22 >> 32
      /* End of loop */

    nop
    /* End of loop */

  /* Accumulate working variables into hash state (vectorized 8x32 addition) */
  bn.mov   w0, w30
  bn.mov   w1, w29
  bn.mov   w2, w23
  bn.mov   w3, w13
  jal      x1, sec_add
  bn.mov   w30, w0
  bn.mov   w29, w1

  ret

.data
.balign 32
bswap32_mask:
  .word 0x000000ff, 0x000000ff, 0x000000ff, 0x000000ff
  .word 0x000000ff, 0x000000ff, 0x000000ff, 0x000000ff

.balign 32
sha256_W_s0: .zero 256
sha256_W_s1: .zero 256

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
