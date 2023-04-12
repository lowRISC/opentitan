/* Copyright lowRISC contributors.
 * Copyright 2016 The Chromium OS Authors. All rights reserved.
 * Use of this source code is governed by a BSD-style license that can be
 * found in the LICENSE.dcrypto file.
 */

/**
 * This library implements hash computation as specified in FIPS PUB 180-4
 * "Secure Hash Standard (SHS)" for the SHA-512 and SHA-384 variants.
 *
 * Terminology within the comments in this library is based (as much as
 * possible) on the terminology of FIPS 180-4.
 *
 * The functions named with the greek sigma have been renamed:
 *   - sigma_lowercase(x) -> s(x)
 *   - sigma_uppercase(x) -> S(x)
 *
 * Upercase W_i denotes the i-th word from the message schedule.
 * Uppercase M_i denotes the i_th message word of the current chunk.
 * Uppercase K_i denotes the i-th round constant.
 *
 * Note on SHA-384: SHA-384 uses the same base algorithm as SHA-512. The
 * only differences are:
 *    - different intial hash values for each variant
 *    - for SHA-384 the message digest is truncated to 384 bit
 *      (only the first 6 final hash values are used)
 * Both aspects are out of scope of this implementation. Therefore, this
 * implementation provides the base algorithm for bose variants.
 */


.section .text


/**
 * Compute SHA-512 (or SHA-384) hash
 *
 * Updates the SHA-512 state for n subsequent 1024-bit chunks of a
 * pre-formatted message.
 *
 * The message is expected in dmem in a pre-processed format:
 *  - The message has been padded according to the SHA-512 standard.
 *  - The padded message has been broken down into 64-bit sized big-endian
 *    words. I.e. for a message stored at dmem address a, the expected
 *    formating for the first 16 message bytes is as follows
 *    (where mn denotes the n-th message byte):
 *    |a+15|a+14|a+13|a+12|a+11|a+10|a+9|a+8|a+7|a+6|a+5|a+4|a+3|a+2|a+1|a+0|
 *    |  m8|  m9| m10| m11| m12| m13|m14|m15| m0| m1| m2| m3| m4| m5| m6| m7|
 *
 * The state variables H[0] to H[7] are expected in dmem in 8 subsequent
 * 256-bit memory cells, where each state variable occupies the lower 64 bit
 * of such a cell. For the state stored at dmem address a the expected format
 * is as follows:
 *  dmem[a +    ][63:0]: H[0]
 *  dmem[a +  32][63:0]: H[1]
 *  dmem[a +  64][63:0]: H[2]
 *  dmem[a +  96][63:0]: H[3]
 *  dmem[a + 128][63:0]: H[4]
 *  dmem[a + 160][63:0]: H[5]
 *  dmem[a + 192][63:0]: H[6]
 *  dmem[a + 224][63:0]: H[7]
 * The upper 192 bits of each cell are clobbered during the execution of the
 * algorithm but their contents are irrelevant.
 *
 * The routine makes use of a 640 byte sized scratchpad in dmem for the message
 * schedule.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[n_chunks]: number of chunks to process in a single go
 * @param[in]  dmem[dptr_state]: dmem location with state      ][63:0]: H[0]
 * @param[in]  dmem[dptr_msg]: Pointer to memory location containing the pre-
 *                               formatted message chunks.
 *
 * clobbered registers: w0 to w7, w10, w11, w15 to w26, w30, w31
 *                      x1, x2, x10, x11 to x17, x20
 * clobbered flag groups: FG0
 */
.globl sha512
sha512:

  /* w31 = 0; w30 = 1111...1111 */
  bn.xor  w31, w31, w31
  bn.subi w30, w31, 1

  /* read number of 1024-bit chunks from dmem */
  la x20, n_chunks
  lw x20, 0(x20)

  /* read pointer to state variables from dmem */
  la x17, dptr_state
  lw x17, 0(x17)

  /* read pointer to message buffer from dmem */
  la x14, dptr_msg
  lw x14, 0(x14)

  /* init reg pointers */
  li x10, 10
  li x11, 11
  li x19, 22

  /* init pointer to scratchpad for message schedule */
  la x13, W

  /* init pointer to round constants */
  la x16, K

  /* one iteration per chunk */
  loop x20, 369

    /* reset pointer to message schedule */
    addi x12, x13, 0

    /* Expand 1024 bit data chunk to full message schedule (W_0 ... W_79)
       The 80 64-bit words of the message schedule are kept in dmem
       scatchpad (20 256-bit cells). */

    /* The message schedule's 16 lower words (W_0 to W_15) are set equal to the
       16 words of the message chunk (M_0 to M_15).

       The WDRs w19 to w22 are used as a sliding window over 16 words of the
       message schedule and are initialized as follows:
       w19 <=  W_3  | W_2  | W_1  | W_0
       w20 <=  W_7  | W_6  | W_5  | W_4
       w21 <=  W_11 | W_10 | W_9  | W_8
       w22 <=  W_15 | W_14 | W_13 | W_12 */
    addi    x2, x0, 19
    loopi   4, 3
      bn.lid  x2, 0(x14++)
      bn.sid  x2, 0(x12++)
      addi    x2, x2, 1

    /* The remaining 74 words are constructed from the lower 16 ones:
       W_t = s1(W_(t-2)) + W_(t-7) + s0(W_(t-15)) + W_(t-16)
       with:
       s0(x) = (x RROT 1) xor (x RROT 8) xor (x SHR 7)
       s1(x) = (x RROT 19) xor (x RROT 61) xor (x SHR 6) */

    /* In the loop body below, i denotes to the i-th cycle of this loop,
       t refers to the index t as used in the FIPS document. Each loop
       cycle computes 4 new words of the message schedule. Hence, i runs from
       0 to 15, and t runs from 16 to 79.
       Note that the assignments in comments only show the relevant 64 bit for
       each operation. The remaining bits are (usually) clobbered as well but
       are irrelevant for further processing. */
    loopi   16, 74

      /* t <= i*4 + 16 */

      /* Window register contents (w19 to w22) at start of cycle:
         w19 = W_(i*4+3)  | W_(i*4+2)  | W_(i*4+1)  | W_(i*4)
             = W_(t-13)   | W_(t-14)   | W_(t-15)   | W_(t-16)
         w20 = W_(i*4+7)  | W_(i*4+6)  | W_(i*4+5)  | W_(i*4+4)
             = W_(t-9)    | W_(t-10)   | W_(t-11)   | W_(t-12)
         w21 = W_(i*4+11) | W_(i*4+10) | W_(i*4+9)  | W_(i*4+8)
             = W_(t-5)    | W_(t-6)    | W_(t-7)    | W_(t-8)
         w22 = W_(i*4+15) | W_(i*4+14) | W_(i*4+13) | W_(i*4+12)
             = W_(t-1)    | W_(t-2)    | W_(t-3)    | W_(t-4) */

      /* w15[255:192] <= s0( W_(t-15) )
           = (W_(t-15) ROTR 1) XOR (W_(t-15) ROTR 8) XOR (W_(t-15) SHR 8) */
      bn.rshi  w18, w19, w30 >> 128
      bn.rshi  w17, w30, w19 >> 64
      bn.rshi  w15, w17, w18 >> 1
      bn.rshi  w16, w17, w18 >> 8
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w18 >> 7
      bn.xor   w15, w15, w16

      /* w23[63:0] <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) */
      bn.add   w23, w19, w15 >> 192
      bn.add   w23, w23, w21 >> 64

      /* w15[255:192] <= s1( W_(t-2) )
           = (W_(t-2) ROTR 19) XOR (W_(t-2) ROTR 61) XOR (W_(t-2) SHR 6) */
      bn.rshi  w18, w22, w30  >> 192
      bn.rshi  w17, w30, w22  >> 128
      bn.rshi  w15, w17, w18  >> 19
      bn.rshi  w16, w17, w18  >> 61
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w18  >> 6
      bn.xor   w15, w15, w16

      /* w23[63:0] = w_t
                   <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) + s1( W_(t-2) ) */
      bn.add   w23, w23, w15 >> 192


      /* t <= i*4 + 17
         w19       = W_(t-14) | W_(t-15) | W_(t-16) | W_(t-17)
         w20       = W_(t-10) | W_(t-11) | W_(t-12) | W_(t-13)
         w21       = W_(t-6)  | W_(t-7) |  W_(t-8)  | W_(t-9)
         w22       = W_(t-2)  | W_(t-3)  | W_(t-4)  | W_(t-5)
         w23[63:0] = W_(t-1) */

      /* w15[255:192] <= s0( W_(t-15) )
           = (W_(t-15) ROTR 1) XOR (W_(t-15) ROTR 8) XOR (W_(t-15) SHR 8) */
      bn.rshi  w18, w19, w30  >> 192
      bn.rshi  w17, w30, w19  >> 128
      bn.rshi  w15, w17, w18  >> 1
      bn.rshi  w16, w17, w18  >> 8
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w18  >> 7
      bn.xor   w15, w15, w16

      /* w24[63:0] <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) */
      bn.add   w24, w31, w19 >> 64
      bn.add   w24, w24, w15 >> 192
      bn.add   w24, w24, w21 >> 128

      /* w15[255:192] <= s1( W_(t-2) )
           = (W_(t-2) ROTR 19) XOR (W_(t-2) ROTR 61) XOR (W_(t-2) SHR 6) */
      bn.rshi  w17, w30, w22  >> 192
      bn.rshi  w15, w17, w22  >> 19
      bn.rshi  w16, w17, w22  >> 61
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w22  >> 6
      bn.xor   w15, w15, w16

      /* w24[63:0] = w_t
                   <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) + s1( W_(t-2) ) */
      bn.add   w24, w24, w15 >> 192


      /* t = i*4 + 18
         w19       = W_(t-15) | W_(t-16) | W_(t-17) | W_(t-18)
         w20       = W_(t-11) | W_(t-12) | W_(t-13) | W_(t-14)
         w21       = W_(t-7)  | W_(t-8) |  W_(t-9)  | W_(t-10)
         w22       = W_(t-3)  | W_(t-4)  | W_(t-5)  | W_(t-6)
         w23[63:0] = W_(t-2)
         w24[63:0] = W_(t-1) */

      /* w15[255:192] <= s0( W_(t-15) )
           = (W_(t-15) ROTR 1) XOR (W_(t-15) ROTR 8) XOR (W_(t-15) SHR 8) */
      bn.rshi  w17, w30, w19  >> 192
      bn.rshi  w15, w17, w19  >> 1
      bn.rshi  w16, w17, w19  >> 8
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w19  >> 7
      bn.xor   w15, w15, w16

      /* w25[63:0] <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) */
      bn.add   w25, w31, w19 >> 128
      bn.add   w25, w25, w15 >> 192
      bn.add   w25, w25, w21 >> 192

      /* w15[255:192] <= s1( W_(t-2) )
           = (W_(t-2) ROTR 19) XOR (W_(t-2) ROTR 61) XOR (W_(t-2) SHR 6) */
      bn.rshi  w18, w23, w30  >> 64
      bn.rshi  w15, w23, w18  >> 19
      bn.rshi  w16, w23, w18  >> 61
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w18  >> 6
      bn.xor   w15, w15, w16

      /* w25[63:0] = w_t
                   <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) + s1( W_(t-2) ) */
      bn.add   w25, w25, w15 >> 192


      /* t = i*4 + 19
         w19       = W_(t-16) | W_(t-17) | W_(t-18) | W_(t-19)
         w20       = W_(t-12) | W_(t-13) | W_(t-14) | W_(t-15)
         w21       = W_(t-8)  | W_(t-9) |  W_(t-10) | W_(t-11)
         w22       = W_(t-4)  | W_(t-5)  | W_(t-6)  | W_(t-7)
         w23[63:0] = W_(t-3)
         w24[63:0] = W_(t-2)
         w25[63:0] = W_(t-1) */

      /* w15[255:192] <= s0( W_(t-15) )
           = (W_(t-15) ROTR 1) XOR (W_(t-15) ROTR 8) XOR (W_(t-15) SHR 8) */
      bn.rshi  w18, w20, w30  >> 64
      bn.rshi  w15, w20, w18  >> 1
      bn.rshi  w16, w20, w18  >> 8
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w18  >> 7
      bn.xor   w15, w15, w16

      /* w26[63:0] <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) */
      bn.add   w26, w31, w19 >> 192
      bn.add   w26, w26, w15 >> 192
      bn.add   w26, w26, w22

      /* w15[255:192] <= s1( W_(t-2) )
           = (W_(t-2) ROTR 19) XOR (W_(t-2) ROTR 61) XOR (W_(t-2) SHR 6) */
      bn.rshi  w18, w24, w30  >> 64
      bn.rshi  w15, w24, w18  >> 19
      bn.rshi  w16, w24, w18  >> 61
      bn.xor   w15, w15, w16
      bn.rshi  w16, w31, w18  >> 6
      bn.xor   w15, w15, w16

      /* w26[63:0] = w_t
                   <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) + s1( W_(t-2) ) */
      bn.add   w26, w26, w15 >> 192

      /* Forward window */
      bn.mov   w19, w20
      bn.mov   w20, w21
      bn.mov   w21, w22

      /* Assemble 256-bit cell from the 4 words computed above */
      /* w22 = w26[63:0] | w25[63:0] | w24[63:0] | w23[64:0]
             = W[i*4+19] | W[i*4+18] | W[i*4+17] | W[i*4+16] */
      bn.rshi  w22, w23, w22  >> 64
      bn.rshi  w22, w24, w22  >> 64
      bn.rshi  w22, w25, w22  >> 64
      bn.rshi  w22, w26, w22  >> 64


      /* Store the 4 words in dmem scratchpad */
      bn.sid   x19, 0(x12++)


    /* load state variables from dmem */
    addi     x2, x0, 0
    /* w0[63:0] = a <= H_0 */
    bn.lid   x2++, 0(x17)
    /* w1[63:0] = b <= H_1 */
    bn.lid   x2++, 32(x17)
    /* w2[63:0] = c <= H_2 */
    bn.lid   x2++, 64(x17)
    /* w3[63:0] = d <= H_3 */
    bn.lid   x2++, 96(x17)
    /* w4[63:0] = e <= H_4 */
    bn.lid   x2++, 128(x17)
    /* w5[63:0] = f <= H_5 */
    bn.lid   x2++, 160(x17)
    /* w6[63:0] = g <= H_6 */
    bn.lid   x2++, 192(x17)
    /* w7[63:0] = h <= H_7 */
    bn.lid   x2++, 224(x17)

    /* reset pointer to start of message schedule scratchpad in dmem */
    addi x12, x13, 0

    /* reset pointer to beginning of dmem section containing round constants */
    addi x15, x16, 0

    /* Main loop for SHA compression function. Processes 8 words of message
       schedule in one cycle.
       This saves copying the SHA working variables (a,b,...,h) after each
       word. If code size becomes an issue, the size of the loop body can
       be significantly reduced for the penalty 6 additional instructions after
       each word.
       Below,
         i denotes the current loop cycle, and
         t denotes the current word (hence t=i*8+(0,1,...,7) ). */
    loopi 10, 253

      /* Load four round constants from dmem */
      /* w10 <= [K_(i*8+3),K_(i*8+2),K_(i*8+1),K_(i*8)] = dmem[K + 2*i] */
      bn.lid   x10, 0(x15++)

      /* Load four message schedule words from dmem scratchpad */
      /* w11 <= [W_(i*8+3),W_(i*8+2),W_(i*8+1),W_(i*8)] = dmem[W + 2*i] */
      bn.lid   x11, 0(x12++)

      /* w6[63:0] = g */
      /* w5[63:0] = f */
      /* w4[63:0] = e */
      /* w3[63:0] = d */
      /* w2[63:0] = c */
      /* w1[63:0] = b */
      /* w0[63:0] = a */


      /* Process word 0 of loop cycle: t <= i*8. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w0, w30  >> 64
      bn.rshi  w15,  w0, w22  >> 28
      bn.rshi  w21,  w0, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w0, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w0,  w1
      bn.and   w21,  w0,  w2
      bn.xor   w16, w16, w21
      bn.and   w21,  w1,  w2
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w4, w30  >> 64
      bn.rshi  w18,  w4, w22  >> 14
      bn.rshi  w21,  w4, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w4, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w4,  w5
      bn.not   w21,  w4
      bn.and   w21, w21,  w6
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20, w7
      bn.add   w20, w20, w10
      bn.add   w21, w11, w19
      bn.add   w20, w20, w21

      /* w6[63:0] = h <= g */
      /* w5[63:0] = g <= f */
      /* w4[63:0] = f <= e */
      /* w3[63:0] = e <= d + T1 = w3[63:0] + w20[63:0] */
      bn.add    w3,  w3, w20
      /* w2[63:0] = d <= c */
      /* w1[63:0] = c <= b */
      /* w0[63:0] = b <= a */
      /* w7[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add    w7, w20, w17


      /* Process word 1 of loop cycle: t <= i*8 + 1. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w7, w30  >> 64
      bn.rshi  w15,  w7, w22  >> 28
      bn.rshi  w21,  w7, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w7, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w7,  w0
      bn.and   w21,  w7,  w1
      bn.xor   w16, w16, w21
      bn.and   w21,  w0,  w1
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w3, w30  >> 64
      bn.rshi  w18,  w3, w22  >> 14
      bn.rshi  w21,  w3, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w3, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w3,  w4
      bn.not   w21,  w3
      bn.and   w21, w21,  w5
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w6
      bn.add   w20, w20, w10  >> 64
      bn.rshi  w21, w30, w11  >> 64
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w5[63:0] = h <= g */
      /* w4[63:0] = g <= f */
      /* w3[63:0] = f <= e */
      /* w2[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add w2, w2, w20
      /* w1[63:0] = d <= c */
      /* w0[63:0] = c <= b */
      /* w7[63:0] = b <= a */
      /* w6[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add w6, w20, w17


      /* Process word 2 of loop cycle: t <= i*8 + 2. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w6, w30  >> 64
      bn.rshi  w15,  w6, w22  >> 28
      bn.rshi  w21,  w6, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w6, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w6, w7
      bn.and   w21,  w6, w0
      bn.xor   w16, w16, w21
      bn.and   w21,  w7, w0
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w2, w30  >> 64
      bn.rshi  w18,  w2, w22  >> 14
      bn.rshi  w21,  w2, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w2, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w2,  w3
      bn.not   w21,  w2
      bn.and   w21, w21,  w4
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w5
      bn.add   w20, w20, w10  >> 128
      bn.rshi  w21, w30, w11  >> 128
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w4[63:0] = h <= g */
      /* w3[63:0] = g <= f */
      /* w2[63:0] = f <= e */
      /* w1[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add   w1,  w1, w20
      /* w0[63:0] = d <= c */
      /* w7[63:0] = c <= b */
      /* w6[63:0] = b <= a */
      /* w5[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add   w5, w20, w17


      /* Process word 3 of loop cycle: t <= i*8 + 3. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w5, w30  >> 64
      bn.rshi  w15,  w5, w22  >> 28
      bn.rshi  w21,  w5, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w5, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w5,  w6
      bn.and   w21,  w5,  w7
      bn.xor   w16, w16, w21
      bn.and   w21,  w6,  w7
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w1, w30  >> 64
      bn.rshi  w18,  w1, w22  >> 14
      bn.rshi  w21,  w1, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w1, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w1,  w2
      bn.not   w21,  w1
      bn.and   w21, w21,  w3
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w4
      bn.add   w20, w20, w10  >> 192
      bn.rshi  w21, w30, w11  >> 192
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w3[63:0] = h <= g */
      /* w2[63:0] = g <= f */
      /* w1[63:0] = f <= e */
      /* w0[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add    w0,  w0, w20
      /* w7[63:0] = d <= c */
      /* w6[63:0] = c <= b */
      /* w5[63:0] = b <= a */
      /* w4[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add    w4, w20, w17


      /* Load another four round constants from dmem */
      /* w10 <= [K_(i*8+7),K_(i*8+6),K_(i*8+5),K_(i*8+4)] = dmem[K + 2*i+1] */
      bn.lid x10, 0(x15++)

      /* Load another four message schedule words from dmem scratchpad */
      /* w11 <= [W_(i*8+7),W_(i*8+6),W_(i*8+5),W_(i*8+4)] = dmem[W + 2*i+1] */
      bn.lid x11, 0(x12++)


      /* Process word 4 of loop cycle: t <= i*8 + 3. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w4, w30  >> 64
      bn.rshi  w15,  w4, w22  >> 28
      bn.rshi  w21,  w4, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w4, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w4,  w5
      bn.and   w21,  w4,  w6
      bn.xor   w16, w16, w21
      bn.and   w21,  w5,  w6
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w0, w30  >> 64
      bn.rshi  w18,  w0, w22  >> 14
      bn.rshi  w21,  w0, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w0, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w0,  w1
      bn.not   w21,  w0
      bn.and   w21, w21,  w2
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w3
      bn.add   w20, w20, w10  >> 0
      bn.rshi  w21, w30, w11  >> 0
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w2[63:0] = h <= g */
      /* w1[63:0] = g <= f */
      /* w0[63:0] = f <= e */
      /* w7[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add    w7,  w7, w20
      /* w6[63:0] = d <= c */
      /* w5[63:0] = c <= b */
      /* w4[63:0] = b <= a */
      /* w3[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add    w3, w20, w17


      /* Process word 5 of loop cycle: t <= i*8 + 3. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w3, w30  >> 64
      bn.rshi  w15,  w3, w22  >> 28
      bn.rshi  w21,  w3, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w3, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w3,  w4
      bn.and   w21,  w3,  w5
      bn.xor   w16, w16, w21
      bn.and   w21,  w4,  w5
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16


      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w7, w30  >> 64
      bn.rshi  w18,  w7, w22  >> 14
      bn.rshi  w21,  w7, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w7, w22  >> 41
      bn.xor   w18, w18, w19


      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w7,  w0
      bn.not   w21,  w7
      bn.and   w21, w21,  w1
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w2
      bn.add   w20, w20, w10  >> 64
      bn.rshi  w21, w30, w11  >> 64
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w1[63:0] = h <= g */
      /* w0[63:0] = g <= f */
      /* w7[63:0] = f <= e */
      /* w6[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add    w6,  w6, w20
      /* w5[63:0] = d <= c */
      /* w4[63:0] = c <= b */
      /* w3[63:0] = b <= a */
      /* w2[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add    w2, w20, w17

      /* Process word 6 of loop cycle: t <= i*8 + 3. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w2, w30  >> 64
      bn.rshi  w15,  w2, w22  >> 28
      bn.rshi  w21,  w2, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w2, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w2,  w3
      bn.and   w21,  w2,  w4
      bn.xor   w16, w16, w21
      bn.and   w21,  w3,  w4
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w6, w30  >> 64
      bn.rshi  w18,  w6, w22  >> 14
      bn.rshi  w21,  w6, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w6, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w6,  w7
      bn.not   w21,  w6
      bn.and   w21, w21,  w0
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w1
      bn.add   w20, w20, w10  >> 128
      bn.rshi  w21, w30, w11  >> 128
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w0[63:0] = h <= g */
      /* w7[63:0] = g <= f */
      /* w6[63:0] = f <= e */
      /* w5[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add    w5,  w5, w20
      /* w4[63:0] = d <= c */
      /* w3[63:0] = c <= b */
      /* w2[63:0] = b <= a */
      /* w1[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add    w1, w20, w17


      /* Process word 7 of loop cycle: t <= i*8 + 3. */

      /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
      bn.rshi  w22,  w1, w30  >> 64
      bn.rshi  w15,  w1, w22  >> 28
      bn.rshi  w21,  w1, w22  >> 34
      bn.xor   w15, w15, w21
      bn.rshi  w21,  w1, w22  >> 39
      bn.xor   w15, w15, w21

      /* w16[63:0] = Maj(a,b,c) = (a AND b) XOR (a AND c) XOR (b AND c) */
      bn.and   w16,  w1,  w2
      bn.and   w21,  w1,  w3
      bn.xor   w16, w16, w21
      bn.and   w21,  w2,  w3
      bn.xor   w16, w16, w21

      /* w17[63:0] <= T2 = S0(a) + Maj(a,b,c) = w15[255:192] + w16[63:0] */
      bn.rshi  w17, w30, w15  >> 192
      bn.add   w17, w17, w16

      /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41) */
      bn.rshi  w22,  w5, w30  >> 64
      bn.rshi  w18,  w5, w22  >> 14
      bn.rshi  w21,  w5, w22  >> 18
      bn.xor   w18, w18, w21
      bn.rshi  w19,  w5, w22  >> 41
      bn.xor   w18, w18, w19

      /* w19[63:0] <= Ch(e,f,g) = (e AND f) XOR ((NOT e) AND g) */
      bn.and   w19,  w5,  w6
      bn.not   w21,  w5
      bn.and   w21, w21,  w7
      bn.xor   w19, w19, w21

      /* w20[63:0] <= T1 = h + S1(e) + Ch(e,f,g) + K_t + W_t */
      bn.rshi  w20, w30, w18  >> 192
      bn.add   w20, w20,  w0
      bn.add   w20, w20, w10  >> 192
      bn.rshi  w21, w30, w11  >> 192
      bn.add   w21, w21, w19
      bn.add   w20, w20, w21

      /* w7[63:0] = h <= g */
      /* w6[63:0] = g <= f */
      /* w5[63:0] = f <= e */
      /* w4[63:0] = e <= d + T1 = w2[63:0] + w20[63:0] */
      bn.add w4, w4, w20
      /* w3[63:0] = d <= c */
      /* w2[63:0] = c <= b */
      /* w1[63:0] = b <= a */
      /* w0[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
      bn.add w0, w20, w17



    /* Add compressed chunk to current hash value */
    addi      x2, x0, 15

    /* H_0 <= H_0 + a */
    bn.lid    x2, 0(x17)
    bn.add   w15, w0, w15
    bn.sid    x2, 0(x17)

    /* H_1 <= H_1 + b */
    bn.lid    x2, 32(x17)
    bn.add   w15, w1, w15
    bn.sid    x2, 32(x17)

    /* H_2 <= H_2 + c */
    bn.lid    x2, 64(x17)
    bn.add   w15, w2, w15
    bn.sid    x2, 64(x17)

    /* H_3 <= H_3 + d */
    bn.lid    x2, 96(x17)
    bn.add   w15, w3, w15
    bn.sid    x2, 96(x17)

    /* H_4 <= H_4 + e */
    bn.lid    x2, 128(x17)
    bn.add   w15, w4, w15
    bn.sid    x2, 128(x17)

    /* H_5 <= H_5 + f */
    bn.lid    x2, 160(x17)
    bn.add   w15, w5, w15
    bn.sid    x2, 160(x17)

    /* H_6 <= H_6 + g */
    bn.lid    x2, 192(x17)
    bn.add   w15, w6, w15
    bn.sid    x2, 192(x17)

    /* H_7 <= H_7 + h */
    bn.lid    x2, 224(x17)
    bn.add   w15, w7, w15
    bn.sid    x2, 224(x17)

ret

.bss

/* number of chunks to process */
.globl n_chunks
.balign 4
n_chunks:
  .zero 4

/* pointer to state (dptr_state) */
.globl dptr_state
.balign 4
dptr_state:
  .zero 4

/* pointer to msg (dptr_msg) */
.globl dptr_msg
.balign 4
dptr_msg:
  .zero 4


/* 80*8=640 bytes scratchpad for message schedule */
.section .scratchpad
 .balign 32
W:
 .zero 640

 .data

/* SHA-512 round constants */
.balign 32
K:
.dword 0x428a2f98d728ae22
.dword 0x7137449123ef65cd
.dword 0xb5c0fbcfec4d3b2f
.dword 0xe9b5dba58189dbbc
.dword 0x3956c25bf348b538
.dword 0x59f111f1b605d019
.dword 0x923f82a4af194f9b
.dword 0xab1c5ed5da6d8118
.dword 0xd807aa98a3030242
.dword 0x12835b0145706fbe
.dword 0x243185be4ee4b28c
.dword 0x550c7dc3d5ffb4e2
.dword 0x72be5d74f27b896f
.dword 0x80deb1fe3b1696b1
.dword 0x9bdc06a725c71235
.dword 0xc19bf174cf692694
.dword 0xe49b69c19ef14ad2
.dword 0xefbe4786384f25e3
.dword 0x0fc19dc68b8cd5b5
.dword 0x240ca1cc77ac9c65
.dword 0x2de92c6f592b0275
.dword 0x4a7484aa6ea6e483
.dword 0x5cb0a9dcbd41fbd4
.dword 0x76f988da831153b5
.dword 0x983e5152ee66dfab
.dword 0xa831c66d2db43210
.dword 0xb00327c898fb213f
.dword 0xbf597fc7beef0ee4
.dword 0xc6e00bf33da88fc2
.dword 0xd5a79147930aa725
.dword 0x06ca6351e003826f
.dword 0x142929670a0e6e70
.dword 0x27b70a8546d22ffc
.dword 0x2e1b21385c26c926
.dword 0x4d2c6dfc5ac42aed
.dword 0x53380d139d95b3df
.dword 0x650a73548baf63de
.dword 0x766a0abb3c77b2a8
.dword 0x81c2c92e47edaee6
.dword 0x92722c851482353b
.dword 0xa2bfe8a14cf10364
.dword 0xa81a664bbc423001
.dword 0xc24b8b70d0f89791
.dword 0xc76c51a30654be30
.dword 0xd192e819d6ef5218
.dword 0xd69906245565a910
.dword 0xf40e35855771202a
.dword 0x106aa07032bbd1b8
.dword 0x19a4c116b8d2d0c8
.dword 0x1e376c085141ab53
.dword 0x2748774cdf8eeb99
.dword 0x34b0bcb5e19b48a8
.dword 0x391c0cb3c5c95a63
.dword 0x4ed8aa4ae3418acb
.dword 0x5b9cca4f7763e373
.dword 0x682e6ff3d6b2b8a3
.dword 0x748f82ee5defb2fc
.dword 0x78a5636f43172f60
.dword 0x84c87814a1f0ab72
.dword 0x8cc702081a6439ec
.dword 0x90befffa23631e28
.dword 0xa4506cebde82bde9
.dword 0xbef9a3f7b2c67915
.dword 0xc67178f2e372532b
.dword 0xca273eceea26619c
.dword 0xd186b8c721c0c207
.dword 0xeada7dd6cde0eb1e
.dword 0xf57d4f7fee6ed178
.dword 0x06f067aa72176fba
.dword 0x0a637dc5a2c898a6
.dword 0x113f9804bef90dae
.dword 0x1b710b35131c471b
.dword 0x28db77f523047d84
.dword 0x32caab7b40c72493
.dword 0x3c9ebe0a15c9bebc
.dword 0x431d67c49c100d4c
.dword 0x4cc5d4becb3e42b6
.dword 0x597f299cfc657e2a
.dword 0x5fcb6fab3ad6faec
.dword 0x6c44198c4a475817
