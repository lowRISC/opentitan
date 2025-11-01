/* Copyright lowRISC contributors (OpenTitan project).
 * Copyright 2015 Markku-Juhani O. Saarinen.
 * Use of this source code is governed by the MIT license
 * that can be found in the LICENSE.tiny_sha3 file.
 */

/**
 * This library implements hash computation as specified in FIPS PUB 202
 * "SHA-3 Standard: Permutation-based Hash and Exendable Output Function"
 *
 * The implementation is based on tiny_sha3 by Saarinen.
 * https://github.com/mjosaarinen/tiny_sha3.
 * Terminology within the comments in this library is based (as much as
 * possible) on the terminology of tiny_sha3.
 *
 * SHA-3 context MUST be 32B-aligned. It includes:
 *  -- 200B - data  - offset = 0
 *  --   4B - pt    - offset = 200
 *  --   4B - rsiz  - offset = 204
 *  --   4B - mdlen - offset = 208
 */

.section .text
/**
 * sha3_init
 *
 * Initialize SHA-3 "context".
 *
 * @param[in]  x11: Message digest length
 * @param[in]  w31: all-zero
 * @param[out] x10: Pointer to 212 bytes of memory for holding the context.
                   32B aligned.
 *
 * clobbered registers: x5 to x7
 * clobbered flag groups: none
 */
.global sha3_init
sha3_init:
  addi x5, x10, 0
  addi x6, x0, 31

  /* Initialize the state to all zeros using w31:
     -- 6 * 32  = 192 B
     -- 192 + 8 = 200 B: DONE */
  LOOPI 6, 1
    bn.sid x6, 0(x5++)
  sw x0, 0(x5)
  sw x0, 4(x5)

  /* Save pt, mdlen, rsiz to memory */
  sw   x0, 8(x5)
  slli x6, x11, 1
  addi x7, x0, 200
  sub  x6, x7, x6
  sw   x6, 12(x5)
  sw   x11, 16(x5)
  ret

/**
 * sha3_update
 *
 * Update state with additional data
 *
 * @param[in]    x12: Data length
 * @param[in]    x11: Pointer to data
 * @param[in]    w31: all-zero
 * @param[inout] x10: Pointer to 212 bytes of memory for holding the context.
                   32B aligned.
 *
 * clobbered registers: x5 to x7, x13 to x17, x28 to x31,
 *                      w0 to w13, w21 to w30
 * clobbered flag groups: FG0
 */
.global sha3_update
sha3_update:
  /* Load pt as j */
  lw x5, 200(x10)
  /* Load constant for address alignment */
  li x30, 0xFFFFFFFC
  /* Data counter */
  li x13, 0

  /* The data address is called the 'source address'; while the 'context address
  at pt is called the 'destination address'. We need to compute:
  -- st[j++] ^= data[i] for i=0,...,x12

  Leveraging WDR memory accesses for optimized output writing is hindered by
  data misalignment issues between source and destination addresses, resulting
  in significant code size overhead. Consequently, we opt for byte-wise
  accesses. For peak performance, a dedicated implementation should be explored.

  We iterate over each input byte. As there is only 4B- or 32B-aligned
  load/store, unaligned memory access is tackled by masking the address with
  0xFFFFFFFC to make it 4B-aligned. The the last two bits of the address are
  masked out and used to compute the position of the wanted byte. */
  beq x12, x0, _sha3_update_skip_loop
  LOOP x12, 22
    /* Get destination address */
    add  x6, x10, x5
    addi x5, x5, 1
    /* Align destination address and load data */
    and  x7, x6, x30
    lw   x28, 0(x7)
    /* Mask out the lowest 2 bits of destination address
       to compute position of st[j] */
    andi x29, x6, 0x3
    slli x29, x29, 3

    /* Get source address */
    add  x14, x11, x13
    /* Align source address and load data */
    and  x15, x14, x30
    lw   x15, 0(x15)
    /* Mask out the lowest 2 bits of source address
       to compute position of st[j] */
    andi x16, x14, 0x3
    slli x17, x16, 3
    /* Mask out desired byte */
    srl  x17, x15, x17
    andi x17, x17, 0xFF

    /* Shift x17 to position accoring to x29 */
    sll  x17, x17, x29
    xor  x28, x28, x17
    /* Store back to aligned address from x7 */
    sw   x28, 0(x7)

    /* Load rsiz */
    lw   x29, 204(x10)
    sub  x28, x5, x29
    bne  x28, x0, _sha3_update_skip
    jal  x1, keccakf
    xor  x5, x5, x5 /* j = 0 */
_sha3_update_skip:
    addi x13, x13, 1 /* Increment data counter */

_sha3_update_skip_loop:
  sw x5, 200(x10) /* Store j as pt */
  ret

/**
 * sha3_final
 *
 * Finalize and output a hash
 *
 * @param[in]    w31: all-zero
 * @param[out]   x11: Pointer to digest. 4B aligned.
 * @param[inout] x10: Pointer to 212 bytes of memory for holding the context.
                   32B aligned.
 *
 * clobbered registers: x5 to x7, x11 to x12, x28 to x31,
 *                      w0 to w13, w21 to w30
 * clobbered flag groups: FG0
 */
.global sha3_final
sha3_final:
  /* Load constant for address alignment */
  li   x12, 0xFFFFFFFC

  /* 4B-aligned load st[pt] */
  lw   x5, 200(x10)
  add  x5, x10, x5
  and  x6, x5, x12
  lw   x28, 0(x6)
  /* Mask out the lowest 2 bits of the address for the exact offset */
  andi x29, x5, 0x3
  slli x29, x29, 3
  addi x30, x0, 0x06
  sll  x30, x30, x29
  xor  x28, x28, x30
  sw   x28, 0(x6)

  /* 4B-aligned load st[rsiz-1] */
  lw   x5, 204(x10)
  addi x5, x5, -1
  add  x5, x10, x5
  and  x6, x5, x12
  lw   x28, 0(x6)
  /* Mask out the lowest 2 bits of the address for the exact offset */
  andi x29, x5, 0x3
  slli x29, x29, 3
  addi x30, x0, 0x80
  sll  x30, x30, x29
  xor  x28, x28, x30
  sw   x28, 0(x6)

  jal  x1, keccakf

  /* Load mdlen and process floor(mdlen/4) 32-bit values */
  lw   x5, 208(x10)
  srli x6, x5, 2
  addi x7, x10, 0
  LOOP x6, 4
    lw   x28, 0(x7)
    addi x7, x7, 4
    sw   x28, 0(x11)
    addi x11, x11, 4
  ret

/**
 * shake_xof
 *
 * Switch to SHAKE operation mode
 *
 * @param[in]    w31: all-zero
 * @param[inout] x10: pointer to 212 bytes of memory for holding the context.
                   32B aligned.
 *
 * clobbered registers: x5 to x6, x12, x28 to x31,
 *                      w0 to w13, w21 to w30
 * clobbered flag groups: FG0
 */
.global shake_xof
shake_xof:
  /* Load constant for address alignment */
  li   x12, 0xFFFFFFFC

  /* 4B-aligned load st[pt] */
  lw   x5, 200(x10)
  add  x5, x10, x5
  and  x6, x5, x12
  lw   x28, 0(x6)
  /* Mask out the lowest 2 bits of the address for the exact offset */
  andi x29, x5, 0x3
  slli x29, x29, 3
  addi x30, x0, 0x1F
  sll  x30, x30, x29
  xor  x28, x28, x30
  sw   x28, 0(x6)

  /* 4B-aligned load st[rsiz-1] */
  lw   x5, 204(x10)
  addi x5, x5, -1
  add  x5, x10, x5
  and  x6, x5, x12
  lw   x28, 0(x6)
  /* Mask out the lowest 2 bits of the address for the exact offset */
  andi x29, x5, 0x3
  slli x29, x29, 3
  addi x30, x0, 0x80
  sll  x30, x30, x29
  xor  x28, x28, x30
  sw   x28, 0(x6)

  jal  x1, keccakf
  sw   x0, 200(x10)
  ret

/**
 * shake_out
 *
 * Get SHAKE output
 *
 * @param[in]    x12: desired output length
 * @param[in]    x11: output pointer
 * @param[in]    w31: all-zero
 * @param[inout] x10: pointer to 212 bytes of memory for holding the context.
                   32B aligned.
 *
 * clobbered registers: x5 to x7, x13 to x17, x28 to x31,
 *                      w0 to w13, w21 to w30
 * clobbered flag groups: FG0
 */
.global shake_out
shake_out:
  /* Load pt as j */
  lw   x5, 200(x10)
  /* As mentioned in the comment for sha3_update, using WDR memory accesses for
  optimized output writing is cumbersome due to data misalignment issues between
  source and destination addresses, resulting in significant code size overhead.
  Thus, we opt for byte-wise accesses. */
  /* Load constant for address alignment */
  li   x30, 0xFFFFFFFC
  li   x17, -1
  /* Data counter */
  li   x13, 0

  beq  x12, x0, _shake_out_skip_loop
  LOOP x12, 27
    /* Load rsiz */
    lw   x29, 204(x10)
    sub  x28, x5, x29
    srli x28, x28, 31
    bne  x28, x0, _shake_out_skip

    jal  x1, keccakf
    xor  x5, x5, x5 /* j = 0 */

_shake_out_skip:
    /* 4B-aligned load from source address */
    add  x7, x5, x10
    addi x5, x5, 1
    and  x28, x7, x30
    lw   x28, 0(x28)
    /* Mask out the lowest 2 bits of the address for the exact offset */
    andi x7, x7, 0x3
    slli x7, x7, 3
    srl  x28, x28, x7
    andi x28, x28, 0xFF

    /* 4B-aligned load from destination address */
    add  x7, x11, x13
    addi x13, x13, 1
    and  x16, x7, x30
    lw   x29, 0(x16)
    /* Mask out the lowest 2 bits of the address for the exact offset */
    andi x14, x7, 0x3
    slli x14, x14, 3
    /* Clear index for insertion */
    addi x31, x0, 0xFF
    sll  x15, x31, x14
    xor  x15, x17, x15
    and  x29, x29, x15

    /* Insert */
    sll  x28, x28, x14
    or   x29, x29, x28

    /* Aligned store to output */
    sw   x29, 0(x16)

_shake_out_skip_loop:
  /* Store j as pt */
  sw x5, 200(x10)
  ret

/**
 * Compute Keccak-f permutation
 *
 * @param[in] x10: Pointer to context
 * @param[in] w31: all-zero
 *
 * clobbered registers: x5 to x6, x28 to x29, x31,
 *                      w0 to w13, w21 to w30
 * clobbered flag groups: FG0
 *
 * Upercase L_i denotes the i-th lane from the state array.
 * ^ denotes exclusive-OR
 * & denotes logical AND
 * << denotes left shift
 */

.global keccakf
keccakf:
  /* Copy context pointer */
  add     x5, x0, x10

  /* Load necessary constants:
     w11 <= (1 <<  64) - 1
     w12 <= (1 << 256) - 1
     w13 <= mask_top_1 */
  bn.not  w12, w31
  bn.rshi w11, w31, w12 >> 192
  li      x29, 13
  la      x31, mask_top_1
  bn.lid  x29, 0(x31)

  /* Load input message bytes from dmem */
  /* w0  <= |L_3  |L_2 |L_1 |L_0 |
     w1  <= |L_7  |L_6 |L_5 |L_4 |
     w2  <= |L_11 |L_10|L_9 |L_8 |
     w3  <= |L_15 |L_14|L_13|L_12|
     w29 <= |L_19 |L_18|L_17|L_16|
     w4  <= |L_23 |L_22|L_21|L_20|
     w6  <= |mdlen|rsiz|pt  |L_24| */
  li      x31, 28
  li      x29, 29
  li      x28, 0
  bn.lid  x28, 0(x5++)
  addi    x28, x28, 1
  bn.lid  x28, 0(x5++)
  addi    x28, x28, 1
  bn.lid  x28, 0(x5++)
  addi    x28, x28, 1
  bn.lid  x28, 0(x5++)
  bn.lid  x29, 0(x5++)
  addi    x28, x28, 1
  bn.lid  x28, 0(x5++)
  addi    x28, x28, 2
  bn.lid  x28, 0(x5++)

  /* In order to vectorize logical operations in Keccak-f, input lanes need to be arranged in a specific order as follows:
     w0 <= |L_3 |L_2 |L_1 |L_0 |
     w1 <= |L_8 |L_7 |L_6 |L_5 |
     w2 <= |L_13|L_12|L_11|L_10|
     w3 <= |L_18|L_17|L_16|L_15|
     w4 <= |L_23|L_22|L_21|L_20|
     w5 <= |L_19|L_14|L_9 |L_4 |
     w6 <= |0   |0   |0   |L_24|  */
  bn.and  w5, w1, w11
  bn.and  w30, w2, w11 << 64
  bn.xor  w5, w5, w30
  bn.and  w30, w3, w11 << 128
  bn.xor  w5, w5, w30
  bn.and  w30, w29, w11 << 192
  bn.xor  w5, w5, w30
  bn.rshi w1, w2, w1 >> 64
  bn.rshi w2, w3, w2 >> 128
  bn.rshi w3, w29, w3 >> 192
  bn.and  w6, w6, w11

  /* Load round constants address */
  la      x6, rc

  /* Start 24 rounds of Keccak-f */
  LOOPI 24, 180
    /***** STEP 1: THETA *****/
    /* w7.i <= L_i ^ L_(i+5) ^ L_(i+10) ^ L_(i+15) ^ L_(i+20) = bc_i */
    bn.xor  w7, w0, w1
    bn.xor  w7, w7, w2
    bn.xor  w7, w7, w3
    bn.xor  w7, w7, w4

    /* w8.0 <= L_4 ^ L_9 ^ L_14 ^ L_19 ^ L_24 = bc_4 */
    bn.xor  w8, w5, w5 >> 64
    bn.xor  w8, w8, w5 >> 128
    bn.xor  w8, w8, w5 >> 192
    bn.xor  w8, w8, w6

    /* w29.0 <= w8.0 = bc_4
       w10.0 <= w7.0 = bc_0
       w9.i  <= bc_((i+1)%5)
       w8    <= bc_3
       w7.i  <= bc_((i+4)%5)
       w29.i <= ROTL64(bc_((i+1)%5), 1)
       w10.0 <= ROTL64(bc_0, 1)*/
    bn.and  w29, w8, w11
    bn.and  w10, w11, w7
    bn.rshi w9, w29, w7 >> 64
    bn.and  w8, w11, w7 >> 192
    bn.xor  w7, w29, w7 << 64
    bn.and  w29, w9, w13
    bn.xor  w9, w9, w29
    bn.rshi w29, w31, w29 >> 63
    bn.rshi w9, w9, w31 >> 255
    bn.xor  w9, w9, w29
    bn.xor  w10, w10, w10 << 64
    bn.rshi w10, w31, w10 >> 63
    bn.and  w10, w10, w11

    /* w7.i <= t_i = bc_((i+4) % 5) ^ ROTL64(bc_((i+1) % 5), 1)
       w8   <= t_4 = bc_3 ^ ROTL64(bc_0, 1) */
    bn.xor  w7, w7, w9
    bn.xor  w8, w8, w10

    /* w0.i <= L_i      ^ t_i
       w1.i <= L_(i+5)  ^ t_i
       w2.i <= L_(i+10) ^ t_i
       w3.i <= L_(i+15) ^ t_i
       w4.i <= L_(i+20) ^ t_i
       w5.0 <= L_4      ^ t_4
       w5.1 <= L_9      ^ t_4
       w5.2 <= L_14     ^ t_4
       w5.3 <= L_19     ^ t_4
       w6.0 <= L_24     ^ t_4 */
    bn.xor  w0, w0, w7
    bn.xor  w1, w1, w7
    bn.xor  w2, w2, w7
    bn.xor  w3, w3, w7
    bn.xor  w4, w4, w7
    bn.xor  w5, w5, w8
    bn.xor  w5, w5, w8 << 64
    bn.xor  w5, w5, w8 << 128
    bn.xor  w5, w5, w8 << 192
    bn.xor  w6, w6, w8

    /***** STEP 2-3: RHO-PI *****/
    /* In this step, the lanes are rotated differently. Thus the circular rotation of many lanes cannot be vectorized. We need to perform the rotation individually on each lane.

       w0  = |L_3 |L_2 |L_1 |L_0 |      w27 = |L'_3 |L'_2 |L'_1 |L'_0 |
       w1  = |L_8 |L_7 |L_6 |L_5 |      w26 = |L'_8 |L'_7 |L'_6 |L'_5 |
       w2  = |L_13|L_12|L_11|L_10|      w25 = |L'_13|L'_12|L'_11|L'_10|
       w3  = |L_18|L_17|L_16|L_15| ===> w24 = |L'_18|L'_17|L'_16|L'_15|
       w4  = |L_23|L_22|L_21|L_20|      w23 = |L'_23|L'_22|L'_21|L'_20|
       w5  = |L_19|L_14|L_9 |L_4 |      w22 = |L'_19|L'_14|L'_9 |L'_4 |
       w6  = |0   |0   |0   |L_24|      w21 = |0    |0    |0    |L'_24|

       ====>
       w27 = |ROTL64(L_18,21)|ROTL64(L_12,43)|ROTL64(L_6,44) |L_0            |
       w26 = |ROTL64(L_16,45)|ROTL64(L_10,3) |ROTL64(L_9,20) |ROTL64(L_3,28) |
       w25 = |ROTL64(L_19,8) |ROTL64(L_13,25)|ROTL64(L_7,6)  |ROTL64(L_1,1)  |
       w24 = |ROTL64(L_17,15)|ROTL64(L_11,10)|ROTL64(L_5,36) |ROTL64(L_4,27) |
       w23 = |ROTL64(L_15,41)|ROTL64(L_14,39)|ROTL64(L_8,55) |ROTL64(L_2,62) |
       w22 = |ROTL64(L_23,56)|ROTL64(L_20,18)|ROTL64(L_22,61)|ROTL64(L_24,14)|
       w21 = |0              |0              |0              |ROTL64(L_21,2) |*/
    /* copy L_0 to w27 */
    bn.rshi w27, w0, w31 >> 64

    /* w25.0 <= L'_10 = ROTL64(L_1, 1) */
    bn.and  w29, w11, w0 >> 64
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 63
    bn.rshi w25, w29, w31 >> 64

    /* w23.0 <= L'_20 = ROTL64(L_2, 62) */
    bn.and  w29, w11, w0 >> 128
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 2
    bn.rshi w23, w29, w31 >> 64

    /* w26.0 <= L'_5 = ROTL64(L_3, 28) */
    bn.and  w29, w11, w0 >> 192
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 36
    bn.rshi w26, w29, w31 >> 64

    /* w24.0 <= L'_15 = ROTL64(L_4, 27) */
    bn.and  w29, w11, w5
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 37
    bn.rshi w24, w29, w31 >> 64

    /* w24.1 <= L'_16 = ROTL64(L_5, 36) */
    bn.and  w29, w11, w1
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 28
    bn.rshi w24, w29, w24 >> 64

    /* w27.1 <= L'_1 = ROTL64(L_6, 44) */
    bn.and  w29, w11, w1 >> 64
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 20
    bn.rshi w27, w29, w27 >> 64

    /* w25.1 <= L'_11 = ROTL64(L_7, 6) */
    bn.and  w29, w11, w1 >> 128
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 58
    bn.rshi w25, w29, w25 >> 64

    /* w23.1 <= L'_21 = ROTL64(L_8, 55) */
    bn.and  w29, w11, w1 >> 192
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 9
    bn.rshi w23, w29, w23 >> 64

    /* w26.1 <= L'_6 = ROTL64(L_9, 20) */
    bn.and  w29, w11, w5 >> 64
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 44
    bn.rshi w26, w29, w26 >> 64

    /* w26.2 <= L'_7 = ROTL64(L_10, 3) */
    bn.and  w29, w11, w2
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 61
    bn.rshi w26, w29, w26 >> 64

    /* w24.2 <= L'_17 = ROTL64(L_11, 10) */
    bn.and  w29, w11, w2 >> 64
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 54
    bn.rshi w24, w29, w24 >> 64

    /* w27.2 <= L'_2 = ROTL64(L_12, 43) */
    bn.and  w29, w11, w2 >> 128
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 21
    bn.rshi w27, w29, w27 >> 64

    /* w25.2 <= L'_12 = ROTL64(L_13, 25) */
    bn.and  w29, w11, w2 >> 192
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 39
    bn.rshi w25, w29, w25 >> 64

    /* w23.2 <= L'_22 = ROTL64(L_14, 39) */
    bn.and  w29, w11, w5 >> 128
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 25
    bn.rshi w23, w29, w23 >> 64

    /* w23.3 <= L'_23 = ROTL64(L_15, 41) */
    bn.and  w29, w11, w3
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 23
    bn.rshi w23, w29, w23 >> 64

    /* w26.3 <= L'_8 = ROTL64(L_16, 45) */
    bn.and  w29, w11, w3 >> 64
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 19
    bn.rshi w26, w29, w26 >> 64

    /* w24.3 <= L'_18 = ROTL64(L_17, 15) */
    bn.and  w29, w11, w3 >> 128
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 49
    bn.rshi w24, w29, w24 >> 64

    /* w27.3 <= L'_3 = ROTL64(L_18, 21) */
    bn.and  w29, w11, w3 >> 192
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 43
    bn.rshi w27, w29, w27 >> 64

    /* w25.3 <= L'_13 = ROTL64(L_19, 8) */
    bn.and  w29, w11, w5 >> 192
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 56
    bn.rshi w25, w29, w25 >> 64

    /* w22.0 <= L'_4 = ROTL64(L_24, 14) */
    bn.or   w29, w6, w6 << 64
    bn.rshi w29, w31, w29 >> 50
    bn.rshi w22, w29, w31 >> 64

    /* w22.1 <= L'_9 = ROTL64(L_22, 61) */
    bn.and  w29, w11, w4 >> 128
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 3
    bn.rshi w22, w29, w22 >> 64

    /* w22.2 <= L'_14 = ROTL64(L_20, 18) */
    bn.and  w29, w11, w4
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 46
    bn.rshi w22, w29, w22 >> 64

    /* w22.3 <= L'_19 = ROTL64(L_23, 56) */
    bn.and  w29, w11, w4 >> 192
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 8
    bn.rshi w22, w29, w22 >> 64

    /* w21.0 <= L'_24 = ROTL64(L_21, 2) */
    bn.and  w29, w11, w4 >> 64
    bn.or   w29, w29, w29 << 64
    bn.rshi w29, w31, w29 >> 62
    bn.and  w21, w29, w11

    /***** STEP 4: CHI *****/
    /* Make a copy of w22 for later use */
    bn.mov  w29, w22

    /* bc_i  = L'_i for i=0,1,2,3,4
       w8    = |L'_0|0|0|0|
       w29   = |L'_1|L'_19|L'_14|L'_9|
       w27.i  = L'_i ^ ((~bc_((i+1)%5)) & bc_((i+2)%5)) */
    bn.rshi w7, w29, w27 >> 64
    bn.rshi w8, w27, w31 >> 64
    bn.rshi w29, w7, w29 >> 64
    bn.rshi w30, w27, w7 >> 64
    bn.xor  w7, w7, w12
    bn.and  w30, w30, w7
    bn.xor  w27, w27, w30

    /* bc_i  = L'_(i+5) for i=0,1,2,3,4
       w8    = |L'_5|L'_0|0|0|
       w29   = L'_6|L'_1|L'_19|L'_14|
       w26.i = L'_(i+5) ^ ((~bc_((i+1)%5)) & bc_((i+2)%5)) */
    bn.rshi w7, w29, w26 >> 64 /* st[9876] */
    bn.rshi w8, w26, w8 >> 64 /* st[5 0] */
    bn.rshi w29, w7, w29 >> 64 /* st[6 1 19 14] */
    bn.rshi w30, w26, w7 >> 64 /* st[5987] */
    bn.xor  w7, w7, w12
    bn.and  w30, w30, w7
    bn.xor  w26, w26, w30

    /* bc_i  = L'_(i+10) for i=0,1,2,3,4
       w8    = |L'_10|L'_5|L'_0|0|
       w29   = L'_11|L'_6|L'_1|L'_19|
       w25.i = L'_(i+10) ^ ((~bc_((i+1)%5)) & bc_((i+2)%5)) */
    bn.rshi w7, w29, w25 >> 64
    bn.rshi w8, w25, w8 >> 64
    bn.rshi w29, w7, w29 >> 64
    bn.rshi w30, w25, w7 >> 64
    bn.xor  w7, w7, w12
    bn.and  w30, w30, w7
    bn.xor  w25, w25, w30

    /* bc_i  = L'_(i+15) for i=0,1,2,3,4
       w8    = |L'_15|L'_10|L'_5|L'_0|
       w29   = |L'_16|L'_11|L'_6|L'_1|
       w24.i = L'_(i+15) ^ ((~bc_((i+1)%5)) & bc_((i+2)%5)) */
    bn.rshi w7, w29, w24 >> 64
    bn.rshi w8, w24, w8 >> 64
    bn.rshi w29, w7, w29 >> 64
    bn.rshi w30, w24, w7 >> 64
    bn.xor  w7, w7, w12
    bn.and  w30, w30, w7
    bn.xor  w24, w24, w30

    /* bc_i  = L'_(5i) for i=0,1,2,3,4
       w8    = |L'_15|L'_10|L'_5|L'_0|
       w29   = |L'_16|L'_11|L'_6|L'_1|
       w22.i = L'_(5i+4) ^ ((~bc_(5i)) & L_(5i+1)) */
    bn.xor  w8, w8, w12
    bn.and  w29, w29, w8
    bn.xor  w22, w22, w29

    /* bc_i  = L'_(i+20) for i=0,1,2,3,4
       w29   = |0|0|0|L'_20|
       w8    = |0|0|0|L'_21|
       w23.i = L'_(i+20) ^ ((~bc_((i+1)%5)) & bc_((i+2)%5)) */
    bn.rshi w7, w21, w23 >> 64
    bn.and  w29, w23, w11
    bn.and  w8, w7, w11
    bn.rshi w30, w23, w7 >> 64
    bn.xor  w7, w7, w12
    bn.and  w30, w30, w7
    bn.xor  w23, w23, w30

    /* w21.i = L'_24 ^ ((~L'_20) & L'_21) */
    bn.xor  w29, w29, w11
    bn.and  w29, w29, w8
    bn.xor  w21, w21, w29

    /***** STEP 5: IOTA *****/
    /* L_0 ^= rc[round] */
    bn.lid x31, 0(x6++)
    bn.xor w27, w27, w28

    /* Copy L'_i back to L_i for next round */
    bn.mov w0, w27
    bn.mov w1, w26
    bn.mov w2, w25
    bn.mov w3, w24
    bn.mov w4, w23
    bn.mov w5, w22
    bn.mov w6, w21

  /* Reset context pointer */
  addi   x5, x5, -224

  /* Arrange outputs in WDRs so that they can be saved to the memory:
     w0  = |L_3 |L_2 |L_1 |L_0 |      w0  = |L_3  |L_2 |L_1 |L_0 |
     w1  = |L_8 |L_7 |L_6 |L_5 |      w1  = |L_7  |L_6 |L_5 |L_4 |
     w2  = |L_13|L_12|L_11|L_10|      w2  = |L_11 |L_10|L_9 |L_8 |
     w3  = |L_18|L_17|L_16|L_15| ===> w3  = |L_15 |L_14|L_13|L_12|
     w4  = |L_23|L_22|L_21|L_20|      w4  = |L_19 |L_18|L_17|L_16|
     w5  = |L_19|L_14|L_9 |L_4 |      w5  = |L_23 |L_22|L_21|L_20|
     w6  = |0   |0   |0   |L_24|      w6  = |mdlen|rsiz|pt  |L_24| */
  li     x28, 0
  bn.sid x28, 0(x5++)
  bn.and w29, w5, w11
  bn.xor w29, w29, w1 << 64
  bn.sid x29, 0(x5++)
  bn.and w29, w5, w11 << 64
  bn.xor w29, w29, w1 >> 192
  bn.xor w29, w29, w2 << 128
  bn.sid x29, 0(x5++)
  bn.and w29, w5, w11 << 128
  bn.xor w29, w29, w2 >> 128
  bn.xor w29, w29, w3 << 192
  bn.sid x29, 0(x5++)
  bn.and w29, w5, w11 << 192
  bn.xor w29, w29, w3 >> 64
  bn.sid x29, 0(x5++)
  li     x28, 4
  bn.sid x28, 0(x5++)
  bn.lid x29, 0(x5)
  bn.not w11, w11
  bn.and w29, w29, w11
  bn.xor w29, w6, w29
  bn.sid x29, 0(x5++)
  ret

.data
.balign 32
mask_top_1:
  .dword 0x8000000000000000
  .dword 0x8000000000000000
  .dword 0x8000000000000000
  .dword 0x8000000000000000
