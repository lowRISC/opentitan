/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Public interface. */
.globl sha256

/**
 * Processes several chunks of a message with SHA-256.
 *
 * The caller must have already padded the message and initialized the hash state
 * before calling this function.
 *
 * This routine expects the message in the same byte-order as FIPS 180-4 (fully
 * big-endian).
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]          x10: dptr_msg, Pointer to padded message in DMEM (512 bits)
 * @param[in]          x30: n, Number of message chunks to process
 * @param[in]  dmem[state]: Initial hash state (256 bits)
 * @param[out] dmem[state]: Final hash state (256 bits)
 *
 * clobbered registers: x2, x3, x10 to x12, x21 to x23, w20 to w30
 * clobbered flag groups: FG0
 */
sha256:
  /* Init all-zero register. */
  bn.xor   w31, w31, w31

  /* Create a 32-bit mask.
       w20 <= 2^32 - 1 */
  bn.not   w20, w31
  bn.rshi  w20, w31, w20 >> 224

  /* Initialize constant wide-register pointers.
       x21 <= 21
       x22 <= 22
       x23 <= 23 */
  li       x21, 21
  li       x22, 22
  li       x23, 23

  /* Load the current hash state.
       w30 <= dmem[state] */
  li       x2, 30
  la       x3, state
  bn.lid   x2, 0(x3)

  /* Load the specialized mask for byte-swaps.
       w29 <= 0x000000ff000000ff000000ff... */
  la       x2, bswap32_mask
  li       x3, 29
  bn.lid   x3, 0(x2)

  /* Repeat the compression function for each chunk of the message. */
  loop     x30, 8
    /* Load the next 512 bits of the message and reverse word-endianness.
         w21 <= bswap32(dmem[x10])
         w22 <= bswap32(dmem[x10 + 32]) */
    bn.lid   x23, 0(x10++)
    jal      x1, bswap32_w23
    bn.movr  x21, x23
    bn.lid   x23, 0(x10++)
    jal      x1, bswap32_w23
    bn.movr  x22, x23

    /* Run the per-block function and update the hash state.
         w30 <= sha256_process_block(w30, w22 || w21) */
    jal      x1, sha256_process_block
    nop

  /* Store the final hash state.
       dmem[state] <= w30 */
  li       x2, 30
  la       x3, state
  bn.sid   x2, 0(x3)

  ret

/**
 * Flip the bytes in each 32-bit word of a 256-bit value.
 *
 * This is useful for big-endian/little-endian conversions. FIPS 180-4 uses
 * big-endian integer representation, and OTBN uses little-endian.
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in,out]   w23: Wide register to flip (modified in-place).
 * @param[in]       w29: Byte-swap mask (0x000000ff, repeated 8x).
 *
 * clobbered registers: w23 to w27
 * clobbered flag groups: FG0
 */
bswap32_w23:
  /* Isolate each byte of each 32-bit word.
       w24 <= byte 0 of each word = a
       w25 <= byte 1 of each word = b
       w26 <= byte 2 of each word = c
       w27 <= byte 3 of each word = d */
  bn.and   w24, w29, w23
  bn.and   w25, w29, w23 >> 8
  bn.and   w26, w29, w23 >> 16
  bn.and   w27, w29, w23 >> 24

  /* Shift/or the bytes back in reversed order.
       w23 <= a || b || c || d */
  bn.or    w23, w25, w24 << 8
  bn.or    w23, w26, w23 << 8
  bn.or    w23, w27, w23 << 8

  ret

/**
 * Performs the core SHA-256 hash computation from FIPS 180-4, section 6.2.2.
 *
 * Consumes 512 bits of a message and updates the 256-bit hash state. The
 * caller must have already padded the message and initialized the hash state
 * before calling this function.
 *
 * Section 4.1.2 defines a few building blocks for SHA2, reproduced here for
 * convenience. In the below definitions, & is bitwise AND, ^ is bitwise XOR, |
 * is bitwise OR, ~ is bitwise NOT, and ROTR is a bitwise rotate-right.
 *   - Ch(x, y, z) = (x & y) ^ ((~ x) ^ z)
 *   - Maj(x, y, z) = (x & y) ^ (x & z) ^ (y & z)
 *   - S0(x) = ROTR(2, x) ^ ROTR(13, x) ^ ROTR(22, x)
 *   - S1(x) = ROTR(6, x) ^ ROTR(11, x) ^ ROTR(25, x)
 *   - sigma0 = ROTR(7, x) ^ ROTR(18, x) ^ (x >> 3)
 *   - sigma1 = ROTR(17, x) ^ ROTR(19, x) ^ (x >> 10)
 *
 * S0 and S1 above are represented in the FIPS docs with a capital sigma; we
 * use S0/S1 here so the distinction is clearer between these and sigma0/sigma1
 * (represented with lowercase sigma in the docs).
 *
 * SHA-256 also uses the 64 32-bit round constants K[0..63], defined in section
 * 4.2.2.
 *
 * The first step is to prepare the message schedule, W. This is an array of 64
 * 32-bit words, such that:
 *   - The first 16 words are the message chunk (W[t] = M[t] for 0 <= t <= 15)
 *   - W[t] = sigma1(W[t-2]) + W[t-7] + sigma0(W[t-15]) + W[t-16] for 16 <= t <= 63
 *
 * Next, we set a,b,c,d,e,f,g,h = H[0]..H[7] and run the following steps for
 * t=0..63. All addition is modulo 2^32.
 *   T1 = h + S1(e) + Ch(e,f,g) + K[t] + W[t]
 *   T2 = S0(a) + Maj(a,b,c)
 *   h = g
 *   g = f
 *   f = e
 *   e = d + T1
 *   d = c
 *   c = b
 *   b = a
 *   a = T1 + T2
 *
 * Finally, we add the working variables into the hash state to update it:
 *   H[0] += a
 *   H[1] += b
 *   H[2] += c
 *   H[3] += d
 *   H[4] += e
 *   H[5] += f
 *   H[6] += g
 *   H[7] += h
 *
 * This routine runs in constant time.
 *
 * Flags: Flags have no meaning beyond the scope of this subroutine.
 *
 * @param[in]  x21: constant, 21
 * @param[in]  x22: constant, 22
 * @param[in]  w20: constant, 2^32 - 1
 * @param[in]  w21: Lower message chunk, M[7] || M[6] || ... || M[0]
 * @param[in]  w22: Upper message chunk, M[15] || M[14] || ... || M[8]
 * @param[in]  w30: H, current hash state
 * @param[in]  w31: all-zero
 * @param[out] w30: Final hash state (256 bits)
 *
 * clobbered registers: x11, x12, w21 to w28, w30
 * clobbered flag groups: FG0
 */
sha256_process_block:
  /* Copy the message into the first 512 bits of the message schedule.
       dmem[sha256_W..sha256_W+64] <= w22 || w21 */
  la       x11, sha256_W
  bn.sid   x21, 0(x11++)
  bn.sid   x22, 0(x11++)

  /* Compute the remaining 48 words of the message schedule.

     Stop every 16 iterations to store 16 32-bit words. The words are stored so
     that the message schedule is in little-endian order; dmem[sha256+t*4] should
     be W[t]. Therefore, the schedule is kept in registers so that the smallest
     indices are at the least significant ends.

     Loop invariants at the start of iteration t (t=16..63):
       x11 = sha256_W + (t * 4)
       w21 = W[t-9] || W[t-10] || ... || W[t-16]  // W[t-9] is in bits 224..255
       w22 = W[t-1] || W[t-2] || ... || W[t-8]    // W[t-1] is in bits 224..255
  */
  loopi    3, 22
    loopi    16, 19
      /* w23 <= W[t-2] */
      bn.and   w23, w20, w22 >> 192
      /* w24 <= W[t-2] << 224 */
      bn.rshi  w24, w23, w31 >> 32

      /* w25[255:224] <= ROTR(17, W[t-2]) */
      bn.rshi  w25, w23, w24 >> 17

      /* w26[255:224] <= ROTR(19, W[t-2]) */
      bn.rshi  w26, w23, w24 >> 19

      /* w24 <= W[t-2] >> 10 */
      bn.rshi  w24, w31, w23 >> 10

      /* w27 <= sigma1(W[t-2]) */
      bn.xor   w27, w24, w25 >> 224
      bn.xor   w27, w27, w26 >> 224

      /* w23 <= W[t-15] */
      bn.and   w23, w20, w21 >> 32
      /* w24 <= W[t-15] << 224 */
      bn.rshi  w24, w23, w31 >> 32

      /* w25[255:224] <= ROTR(7, W[t-15]) */
      bn.rshi  w25, w23, w24 >> 7

      /* w26[255:224] <= ROTR(18, W[t-15]) */
      bn.rshi  w26, w23, w24 >> 18

      /* w24 <= W[t-15] >> 3 */
      bn.rshi  w24, w31, w23 >> 3

      /* w28 <= sigma0(W[t-15]) */
      bn.xor   w28, w24, w25 >> 224
      bn.xor   w28, w28, w26 >> 224

      /* w24[31:0] <= sigma1(W[t-2]) + W[t-7] + sigma0(W[t-15]) + W[t-16] = W[t] */
      bn.add   w24, w27, w22 >> 32
      bn.add   w24, w24, w28
      bn.add   w24, w24, w21

      /* w21 <= W[t-8] || W[t-9] || ... || W[t-15] */
      bn.rshi  w21, w22, w21 >> 32

      /* w22 <= W[t] || W[t-1] || ... || W[t-7] */
      bn.rshi   w22, w24, w22 >> 32

    /* Store the next 512 bits of the schedule.
         dmem[sha256_W+(t-16)*4..sha256_W+t*4] <= W[t] || W[t-1] || ... || W[t-16] */
    bn.sid   x21, 0(x11++)
    bn.sid   x22, 0(x11++)

  /* Copy the state register to use as working variables. The state is 8 32-bit
     words, named a-h in the spec. Note that the representation is big-endian,
     so a is in bits 224..255.
       w23 <= w30 = a || b || c || d || e || f || g || h */
  bn.mov     w23, w30

  /* Get a pointer to the start of the message schedule. */
  la         x11, sha256_W

  /* Get a pointer to the first round constant. */
  la         x12, sha256_K

  /* Main loop; iterate through message schedule and update working variables. */
  loopi      8, 41
    /* Load the next 8 words of the message schedule.
         w21 <= W[t+7] || W[t+6] || ... || W[t] */
    bn.lid     x21, 0(x11++)

    /* Load the next 8 round constants.
         w22 <= K[t+7] || K[t+6] || ... || K[t] */
    bn.lid     x22, 0(x12++)

    loopi      8, 37
      /* w24 <= w23[96:127] = e */
      bn.and   w24, w20, w23 >> 96
      /* w25 <= e << 224 */
      bn.rshi  w25, w24, w31 >> 32

      /* w28[255:224] <= ROTR(6, e) ^ ROTR(11, e) ^ ROTR(25, e) = S1(e) */
      bn.rshi  w26, w24, w25 >> 6
      bn.rshi  w27, w24, w25 >> 11
      bn.rshi  w28, w24, w25 >> 25
      bn.xor   w28, w28, w26
      bn.xor   w28, w28, w27

      /* w26 <= w24 & w23[64:95] = e & f */
      bn.and   w26, w24, w23 >> 64

      /* w27 <= ~w24 & w23[32:63] = (~e) & g */
      bn.not   w24, w24
      bn.and   w27, w24, w23 >> 32

      /* w26 <= (e & f) ^ ((~e) & g) = Ch(e, f, g) */
      bn.xor   w26, w26, w27

      /* w25[31:0] <= h + S1(e) + Ch(e, f, g) + K[t] + W[t] = T1 */
      bn.add   w25, w23, w28 >> 224
      bn.add   w25, w25, w26
      bn.add   w25, w25, w22
      bn.add   w25, w25, w21

      /* w24 <= w23[255:224] = a */
      bn.and   w24, w20, w23 >> 224

      /* w28[255:224] <= ROTR(2, a) ^ ROTR(13, a) ^ ROTR(22, a) = S0(a) */
      bn.rshi  w26, w24, w23 >> 2
      bn.rshi  w27, w24, w23 >> 13
      bn.rshi  w28, w24, w23 >> 22
      bn.xor   w28, w28, w26
      bn.xor   w28, w28, w27

      /* w26 <= w24 & w23[223:192] = a & b */
      bn.and   w26, w24, w23 >> 192

      /* w27 <= w24 & w23[291:160] = a & c */
      bn.and   w27, w24, w23 >> 160

      /* w26 <= (a & b) ^ (a & c) */
      bn.xor   w26, w26, w27

      /* w27 <= w23[223:192] & w23[191:160] = b & c */
      bn.and   w27, w23, w23 >> 32
      bn.and   w27, w20, w27 >> 160

      /* w26 <= (a & b) ^ (a & c) ^ (b & c) = Maj(a,b,c) */
      bn.xor   w26, w26, w27

      /* w26[31:0] <= Maj(a,b,c) + S0(a) = T2 */
      bn.add   w26, w26, w28 >> 224

      /* w26[31:0] <= T1 + T2 */
      bn.add   w26, w25, w26

      /* Shift the working variables one position, filling in T1+T2 in the new
         most significant (a) slot. This correctly updates all the working
         variables (b=a, c=b, etc.) except for e, which is special (e=d+T1).
           w23 <= T1 + T2 || a || b || c || d || e || f || g */
      bn.rshi  w23, w26, w23 >> 32

      /* w24 <= w23[127:96] = d */
      bn.and   w24, w23, w20 << 96

      /* Mask (e=d) out of the working variables.
           w23 <= T1 + T2 || a || b || c || 0 || e || f || g */
      bn.xor   w23, w23, w24

      /* w24 <= T1 + d */
      bn.add   w24, w25, w24 >> 96
      bn.and   w24, w24, w20

      /* Set e=d+T1.
           w23 <= T1 + T2 || a || b || c || d+T1 || e || f || g */
      bn.or    w23, w23, w24 << 96

      /* Shift the message schedule and round constants for the next round.
           w21 <= w21 >> 32
           w22 <= w22 >> 32 */
      bn.rshi  w21, w31, w21 >> 32
      bn.rshi  w22, w31, w22 >> 32

    /* End of outer loop. */
    nop

  /* Add the working variables into the state. This is essentially a vectorized
     add, but we need to adds individually to avoid carries. */

  /* w30 = H[7]+h || H[0] || H[1] || H[2] || H[3] || H[4] || H[5] || H[6] */
  bn.add   w24, w30, w23
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[6]+g || H[7]+h || H[0] || H[1] || H[2] || H[3] || H[4] || H[5] */
  bn.add   w24, w30, w23 >> 32
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[5]+f || H[6]+g || H[7]+h || H[0] || H[1] || H[2] || H[3] || H[4] */
  bn.add   w24, w30, w23 >> 64
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[4]+e || H[5]+f || H[6]+g || H[7]+h || H[0] || H[1] || H[2] || H[3] */
  bn.add   w24, w30, w23 >> 96
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[3]+d || H[4]+e || H[5]+f || H[6]+g || H[7]+h || H[0] || H[1] || H[2] */
  bn.add   w24, w30, w23 >> 128
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[2]+c || H[3]+d || H[4]+e || H[5]+f || H[6]+g || H[7]+h || H[0] || H[1] */
  bn.add   w24, w30, w23 >> 160
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[1]+b || H[2]+c || H[3]+d || H[4]+e || H[5]+f || H[6]+g || H[7]+h || H[0] */
  bn.add   w24, w30, w23 >> 192
  bn.rshi  w30, w24, w30 >> 32

  /* w30 = H[0]+a || H[1]+b || H[2]+c || H[3]+d || H[4]+e || H[5]+f || H[6]+g || H[7]+h */
  bn.add   w24, w30, w23 >> 224
  bn.rshi  w30, w24, w30 >> 32

  ret

.section .scratchpad

/* Message schedule (32*64 = 2048 bits) */
.balign 32
sha256_W:
.zero 256

.data

/* Specialized mask for wide word byte-swaps. */
.balign 32
bswap32_mask:
.word 0x000000ff
.word 0x000000ff
.word 0x000000ff
.word 0x000000ff
.word 0x000000ff
.word 0x000000ff
.word 0x000000ff
.word 0x000000ff

/* Round constants (from FIPS 180-4 section 4.2.2). */
.balign 32
sha256_K:
.word 0x428a2f98
.word 0x71374491
.word 0xb5c0fbcf
.word 0xe9b5dba5
.word 0x3956c25b
.word 0x59f111f1
.word 0x923f82a4
.word 0xab1c5ed5
.word 0xd807aa98
.word 0x12835b01
.word 0x243185be
.word 0x550c7dc3
.word 0x72be5d74
.word 0x80deb1fe
.word 0x9bdc06a7
.word 0xc19bf174
.word 0xe49b69c1
.word 0xefbe4786
.word 0x0fc19dc6
.word 0x240ca1cc
.word 0x2de92c6f
.word 0x4a7484aa
.word 0x5cb0a9dc
.word 0x76f988da
.word 0x983e5152
.word 0xa831c66d
.word 0xb00327c8
.word 0xbf597fc7
.word 0xc6e00bf3
.word 0xd5a79147
.word 0x06ca6351
.word 0x14292967
.word 0x27b70a85
.word 0x2e1b2138
.word 0x4d2c6dfc
.word 0x53380d13
.word 0x650a7354
.word 0x766a0abb
.word 0x81c2c92e
.word 0x92722c85
.word 0xa2bfe8a1
.word 0xa81a664b
.word 0xc24b8b70
.word 0xc76c51a3
.word 0xd192e819
.word 0xd6990624
.word 0xf40e3585
.word 0x106aa070
.word 0x19a4c116
.word 0x1e376c08
.word 0x2748774c
.word 0x34b0bcb5
.word 0x391c0cb3
.word 0x4ed8aa4a
.word 0x5b9cca4f
.word 0x682e6ff3
.word 0x748f82ee
.word 0x78a5636f
.word 0x84c87814
.word 0x8cc70208
.word 0x90befffa
.word 0xa4506ceb
.word 0xbef9a3f7
.word 0xc67178f2

/* Working state. */
.balign 32
.globl state
.weak state
state:
.zero 32
