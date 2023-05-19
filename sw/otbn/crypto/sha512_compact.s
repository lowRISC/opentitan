/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * This library implements hash computation as specified in FIPS PUB 180-4
 * "Secure Hash Standard (SHS)" for the SHA-512 and SHA-384 variants.
 *
 * This implementation is a code size and memory optimized
 * variant at the cost of additional computation time.
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
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  dmem[n_chunks]: number of chunks to process in a single go
 * @param[in]  dmem[dptr_state]: dmem location with state      ][63:0]: H[0]
 * @param[in]  dmem[dptr_msg]: Pointer to memory location containing the pre-
 *                               formatted message chunks.
 *
 * clobbered registers: w0 to w7, w10, w11, w15 to w27, w31
 *                      x1, x2, x10, x11 to x17, x20
 * clobbered flag groups: FG0
 */
.globl sha512_compact
sha512_compact:

  /* w31 = 0 */
  bn.xor  w31, w31, w31

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
  li x19, 27

  /* init pointer to round constants */
  la x16, K

  /* one iteration per chunk */
  loop x20, 105

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

    /* reset pointer to beginning of dmem section containing round constants */
    addi x15, x16, 0

    /* read pointer to message buffer from dmem */
    la x14, dptr_msg
    lw x14, 0(x14)
    /* The message schedule's 16 lower words (W_0 to W_15) are set equal to the
       16 words of the message chunk (M_0 to M_15). */
    addi    x2, x0, 24
    bn.lid  x2++, 0(x14)
    bn.lid  x2++, 32(x14)
    bn.lid  x2++, 64(x14)
    bn.lid  x2++, 96(x14)

   /* Main loop for SHA-512 compression function (80 rounds),
      split into an inner and outer loop here (80=20*4 cycles), since
      every 4 rounds a new set of round constants has to be loaded
      from dmem.
      Below, the index i denotes the current round.
      The 8 SHA working variables are kept in a wide reg each (lower
      64 bits:
      w6[63:0] = h
      w6[63:0] = g
      w5[63:0] = f
      w4[63:0] = e
      w3[63:0] = d
      w2[63:0] = c
      w1[63:0] = b
      w0[63:0] = a */

    loopi 20, 62

      /* Load four round constants from dmem
         w10 <= [K_(i+3),K_(i+2),K_(i+1),K_(i)] = dmem[K + i/4] */
      bn.lid   x10, 0(x15++)

      loopi 4, 59

        /* w15[255:192] = S0(a) = (a ROTR 28) XOR (a ROTR 34) XOR (a ROTR 39) */
        bn.rshi  w22,  w0, w31  >> 64
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
        bn.rshi  w17, w31, w15  >> 192
        bn.add   w17, w17, w16

        /* w18[255:192] <= S1(e) = (e ROTR 14) XOR (e ROTR 18) XOR (e ROTR 41)*/
        bn.rshi  w22,  w4, w31  >> 64
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
        bn.rshi  w20, w31, w18  >> 192
        bn.add   w20, w20, w7
        bn.add   w20, w20, w10
        bn.add   w21, w24, w19
        bn.add   w20, w20, w21

        /* rearrange working variables */
        /* w7[63:0] = h <= g */
        bn.mov    w7, w6
        /* w6[63:0] = g <= f */
        bn.mov    w6, w5
        /* w5[63:0] = f <= e */
        bn.mov    w5, w4
        /* w4[63:0] = e <= d + T1 = w3[63:0] + w20[63:0] */
        bn.add    w4, w3, w20
        /* w3[63:0] = d <= c */
        bn.mov    w3, w2
        /* w2[63:0] = c <= b */
        bn.mov    w2, w1
        /* w1[63:0] = b <= a */
        bn.mov    w1, w0
        /* w0[63:0] = a = T_1 + T_2 = w20[63:0] + w17[63:0] */
        bn.add    w0, w20, w17

        /* switch to next round constant for the next cycle */
        bn.rshi   w10, w31, w10 >> 64

        /* Now, a new word W of the message schedule is computed. This word
           is 16 cycles ahead. (The first 16 Ws are identical to the message
           chunk and a history of 16 Ws is needed to compute the current one.)
           This means that we "overshoot" at the end. For the last 16 cycles
           computing a new W is actually not neccessary. However, this
           allows interleaving this computation with the compression rounds
           omitting usage of scratchpad memory and having a simple control flow.
           The alternative is to precompute the full message schedule and place
           it in scratchpad or have a special treatment for the last 16 loop
           cycles.
           The index t below is assumed to run from 16 to 96, hence t = i+16.

           The Ws are kept in 4 wide regs and form a queue which is advanced
           after the computation of the new W (new W is placed in w27[255:192]).
           w24 <=  W_(t-13) | W_(t-14) | W_(t-15) | W_(t-16)
           w25 <=  W_(t-9)  | W_(t-10) | W_(t-11) | W_(t-12)
           w26 <=  W_(t-5)  | W_(t-6)  | W_(t-7)  | W_(t-8)
           w27 <=  W_(t-1)  | W_(t-2)  | W_(t-3)  | W_(t-4) */

        /* w15[255:192] <= s0( W_(t-15) )
             = (W_(t-15) ROTR 1) XOR (W_(t-15) ROTR 8) XOR (W_(t-15) SHR 8) */
        bn.rshi  w18, w24, w31 >> 128
        bn.rshi  w17, w31, w24 >> 64
        bn.rshi  w15, w17, w18 >> 1
        bn.rshi  w16, w17, w18 >> 8
        bn.xor   w15, w15, w16
        bn.rshi  w16, w31, w18 >> 7
        bn.xor   w15, w15, w16

        /* w23[63:0] <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) */
        bn.add   w23, w24, w15 >> 192
        bn.add   w23, w23, w26 >> 64

        /* w15[255:192] <= s1( W_(t-2) )
             = (W_(t-2) ROTR 19) XOR (W_(t-2) ROTR 61) XOR (W_(t-2) SHR 6) */
        bn.rshi  w18, w27, w31  >> 192
        bn.rshi  w17, w31, w27  >> 128
        bn.rshi  w15, w17, w18  >> 19
        bn.rshi  w16, w17, w18  >> 61
        bn.xor   w15, w15, w16
        bn.rshi  w16, w31, w18  >> 6
        bn.xor   w15, w15, w16

        /* w23[63:0] = w_t
                     <= W_(t-16) + W_(t-7) + s0( W_(t-15) ) + s1( W_(t-2) ) */
        bn.add   w23, w23, w15 >> 192

        /* At the newly computed W to the queue */
        bn.rshi  w24, w25, w24 >> 64
        bn.rshi  w25, w26, w25 >> 64
        bn.rshi  w26, w27, w26 >> 64
        bn.rshi  w27, w23, w27 >> 64

        /* nop to prevent same final instruction in both loop bodies */
        nop


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
.weak n_chunks
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
