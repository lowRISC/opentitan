/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Number-theoretic transform for ML-DSA. */

.global ntt
.global intt

.text

/**
 * In-place transpose of two 8x8 matrices with 32-bit elements held in w[0-7]
 * and w[8-15].
 *
 * @param[in] w0-w7: First 8x8 matrix A0.
 * @param[in] w8-w15: Second 8x8 matrix A1.
 * @param[out] w0-w7: A0^T
 * @param[out] w8-w15: A1^T
 */
_transpose_8x8_w0w16:
  /*
  w0 = [x07,x06,x05,x04,x03,x02,x01,x00] = [x56,x48,x40,x32,x24,x16,x08,x00]
  w1 = [x15,x14,x13,x12,x11,x10,x09,x08] = [x57,x49,x41,x33,x25,x17,x09,x01]
  w2 = [x23,x22,x21,x20,x19,x18,x17,x16] = [x58,x50,x42,x34,x26,x18,x10,x02]
  w3 = [x31,x30,x29,x28,x27,x26,x25,x24] = [x59,x51,x42,x35,x27,x19,x11,x03]
  w4 = [x39,x38,x37,x36,x35,x34,x33,x32] = [x60,x52,x43,x36,x28,x20,x12,x04]
  w5 = [x47,x46,x45,x44,x43,x42,x41,x40] = [x61,x53,x44,x37,x29,x21,x13,x05]
  w6 = [x55,x54,x53,x52,x51,x50,x49,x48] = [x62,x54,x45,x38,x30,x22,x14,x06]
  w7 = [x63,x62,x61,x60,x59,x58,x57,x56] = [x63,x55,x46,x39,x31,x23,x15,x07]
  */
  bn.trn1.8S w16,  w0,  w1
  bn.trn2.8S w17,  w0,  w1
  bn.trn1.8S w18,  w2,  w3
  bn.trn2.8S w19,  w2,  w3
  bn.trn1.8S w20,  w4,  w5
  bn.trn2.8S w21,  w4,  w5
  bn.trn1.8S w22,  w6,  w7
  bn.trn2.8S w23,  w6,  w7
  bn.trn1.4D  w4, w16, w18
  bn.trn2.4D w16, w16, w18
  bn.trn1.4D w18, w17, w19
  bn.trn2.4D w17, w17, w19
  bn.trn1.4D w19, w20, w22
  bn.trn2.4D w20, w20, w22
  bn.trn1.4D w22, w21, w23
  bn.trn2.4D w21, w21, w23
  bn.trn1.2Q  w0,  w4, w19
  bn.trn2.2Q  w4,  w4, w19
  bn.trn1.2Q  w1, w18, w22
  bn.trn2.2Q  w5, w18, w22
  bn.trn1.2Q  w2, w16, w20
  bn.trn2.2Q  w6, w16, w20
  bn.trn1.2Q  w3, w17, w21
  bn.trn2.2Q  w7, w17, w21

  /*
  w08 = [x07,x06,x05,x04,x03,x02,x01,x00] = [x56,x48,x40,x32,x24,x16,x08,x00]
  w09 = [x15,x14,x13,x12,x11,x10,x09,x08] = [x57,x49,x41,x33,x25,x17,x09,x01]
  w10 = [x23,x22,x21,x20,x19,x18,x17,x16] = [x58,x50,x42,x34,x26,x18,x10,x02]
  w11 = [x31,x30,x29,x28,x27,x26,x25,x24] = [x59,x51,x42,x35,x27,x19,x11,x03]
  w12 = [x39,x38,x37,x36,x35,x34,x33,x32] = [x60,x52,x43,x36,x28,x20,x12,x04]
  w13 = [x47,x46,x45,x44,x43,x42,x41,x40] = [x61,x53,x44,x37,x29,x21,x13,x05]
  w14 = [x55,x54,x53,x52,x51,x50,x49,x48] = [x62,x54,x45,x38,x30,x22,x14,x06]
  w15 = [x63,x62,x61,x60,x59,x58,x57,x56] = [x63,x55,x46,x39,x31,x23,x15,x07]
  */
  bn.trn1.8S w16,  w8,  w9
  bn.trn2.8S w17,  w8,  w9
  bn.trn1.8S w18, w10, w11
  bn.trn2.8S w19, w10, w11
  bn.trn1.8S w20, w12, w13
  bn.trn2.8S w21, w12, w13
  bn.trn1.8S w22, w14, w15
  bn.trn2.8S w23, w14, w15
  bn.trn1.4D w12, w16, w18
  bn.trn2.4D w16, w16, w18
  bn.trn1.4D w18, w17, w19
  bn.trn2.4D w17, w17, w19
  bn.trn1.4D w19, w20, w22
  bn.trn2.4D w20, w20, w22
  bn.trn1.4D w22, w21, w23
  bn.trn2.4D w21, w21, w23
  bn.trn1.2Q  w8, w12, w19
  bn.trn2.2Q w12, w12, w19
  bn.trn1.2Q  w9, w18, w22
  bn.trn2.2Q w13, w18, w22
  bn.trn1.2Q w10, w16, w20
  bn.trn2.2Q w14, w16, w20
  bn.trn1.2Q w11, w17, w21
  bn.trn2.2Q w15, w17, w21

  ret

/*
 * Load 64 32-bit polynomial coefficients from DMEM[x20] to w[x21:x21+8].
 * Increments the address register x20 by 256 and the WDR pointer x21 by 8 such
 * that multiple invocations of the routine can be seamlessly chained.
 */
_load_64x32:
  bn.lid x21++, 0(x20)
  bn.lid x21++, 32(x20)
  bn.lid x21++, 64(x20)
  bn.lid x21++, 96(x20)
  bn.lid x21++, 128(x20)
  bn.lid x21++, 160(x20)
  bn.lid x21++, 192(x20)
  bn.lid x21++, 224(x20)
  addi x20, x20, 256
  ret

/*
 * Store 64 32-bit polynomial coefficients from w[x21:x21+8] to DMEM[x20].
 * Increments the address register x20 by 256 and the WDR pointer x21 by 8 such
 * that multiple invocations of the routine can be seamlessly chained.
 */
_store_64x32:
  bn.sid x21++, 0(x20)
  bn.sid x21++, 32(x20)
  bn.sid x21++, 64(x20)
  bn.sid x21++, 96(x20)
  bn.sid x21++, 128(x20)
  bn.sid x21++, 160(x20)
  bn.sid x21++, 192(x20)
  bn.sid x21++, 224(x20)
  addi x20, x20, 256
  ret

/*
A NTT operation over a polynomial of 256 32-bit coefficients consists of 8
layers with each layer computing 128 butterflies, i.e., the twiddle factors are
multiplied with 128 coefficients. The 32 WDRs in OTBN can hold 128 coefficients
in 16 WDRs with the rest being used to hold twiddle factors and intermediate
results. This means that with the exception of Layer 1, one half of each
subsequent Layer 2-8 can be computed completely in-register without the
need to store and load results to DMEM. This 7x1 decomposition of a 8-layer NTT
differs from the 4x4 decomposition first proposed by Becker et al. [1] as it is
more intutive and makes betters use of the register structure of the OTBN.

In the following, the variable xij designates a block of 8 coefficients for
0 < i, j < 8 with xij_k being the k-th coefficient of block xij where 0 < k < 8.
We start with the complete computation of Layer 1 which is stored back into
DMEM followed by the calculation of the upper half (coefficients 0-127) of
Layers 2-7 and the lower half (coefficients 128-255) of Layers 2-7.
The conventional Cooley-Tukey and Gentlemen-Sande butterflies are for the NTT
and INTT transformation respectively.

 Layer 1    Layer 2    Layer 3    Layer 4    Layer 5

|  x00  |  |  x00  |  |  x00  |  |  x00  |  |  x00  |
|  x01  |  |  x01  |  |  x01  |  |  x01  |  |x01*z15|
|  x02  |  |  x02  |  |  x02  |  |x02*z07|  |  x02  |
|  x03  |  |  x03  |  |  x03  |  |x03*z07|  |x03*z16|
|  x04  |  |  x04  |  |x04*z03|  |  x04  |  |  x04  |
|  x05  |  |  x05  |  |x05*z03|  |  x05  |  |x05*z17|
|  x06  |  |  x06  |  |x06*z03|  |x06*z08|  |  x06  |
|  x07  |  |  x07  |  |x07*z03|  |x07*z08|  |x07*z18|
|  x08  |  |x08*z01|  |  x08  |  |  x08  |  |  x08  |
|  x09  |  |x09*z01|  |  x09  |  |  x09  |  |x09*z19|
|  x10  |  |x10*z01|  |  x10  |  |x10*z09|  |  x10  |
|  x11  |  |x11*z01|  |  x11  |  |x11*z09|  |x11*z20|
|  x12  |  |x12*z01|  |x12*z04|  |  x12  |  |  x12  |
|  x13  |  |x13*z01|  |x13*z04|  |  x13  |  |x13*z21|
|  x14  |  |x14*z01|  |x14*z04|  |x14*z10|  |  x14  |
|  x15  |  |x15*z01|  |x15*z04|  |x15*z10|  |x15*z22|

|x16*z00|  |  x16  |  |  x16  |  |  x16  |  |  x16  |
|x17*z00|  |  x17  |  |  x17  |  |  x17  |  |x17*z23|
|x18*z00|  |  x18  |  |  x18  |  |x18*z11|  |  x18  |
|x19*z00|  |  x19  |  |  x19  |  |x19*z11|  |x19*z24|
|x20*z00|  |  x20  |  |x20*z05|  |  x20  |  |  x20  |
|x21*z00|  |  x21  |  |x21*z05|  |  x21  |  |x21*z25|
|x22*z00|  |  x22  |  |x22*z05|  |x22*z12|  |  x22  |
|x23*z00|  |  x23  |  |x23*z05|  |x23*z12|  |x23*z26|
|x24*z00|  |x24*z02|  |  x24  |  |  x24  |  |  x24  |
|x25*z00|  |x25*z02|  |  x25  |  |  x25  |  |x25*z27|
|x26*z00|  |x26*z02|  |  x26  |  |x26*z13|  |  x26  |
|x27*z00|  |x27*z02|  |  x27  |  |x27*z13|  |x27*z28|
|x28*z00|  |x28*z02|  |x28*z06|  |  x28  |  |  x28  |
|x29*z00|  |x29*z02|  |x29*z06|  |  x29  |  |x29*z29|
|x30*z00|  |x30*z02|  |x30*z06|  |x30*z14|  |  x30  |
|x31*z00|  |x31*z02|  |x31*z06|  |x31*z14|  |x31*z30|

Special care has to be taken for Layers 6-8 as the number of times each twiddle
factor is multiplied with a coefficient (4 times for Layer 6, 2 times for Layer
7 and once for Layer 8) is now smaller than the number of coefficients in a WDR.
In order to continue leveraging the SIMD capabilities of the OTBN accelerator,
the coefficients before Layer 6 need to be transposed in chunks of 8x8 matrices
(see `_transpose_8x8_w0w16`). Additionally, in Layer 7 and 8 the twiddle factors
are stored in a transposed ordering to avoid further transpositions of the
coefficients.

                      Layer 6      Layer 7       Layer 8

|x00_0|             |  x00_0  |  |  x00_0   |  |  x00_0   |
|x00_1|             |  x01_0  |  |  x01_0   |  |  x01_0   |
|x00_2|             |  x02_0  |  |  x02_0   |  |  x02_0   |
|x00_3|             |  x03_0  |  |  x03_0   |  |  x03_0   |
|x00_4|             |  x04_0  |  |  x04_0   |  |  x04_0   |
|x00_5|             |  x05_0  |  |  x05_0   |  |  x05_0   |
|x00_6|             |  x06_0  |  |  x06_0   |  |  x06_0   |
|x00_7|             |  x07_0  |  |  x07_0   |  |  x07_0   |
|x01_0|             |  x00_1  |  |  x00_1   |  |  x00_1   |
|x01_1|             |  x01_1  |  |  x01_1   |  |x01_1*z127|
|x01_2|             |  x02_1  |  |  x02_1   |  |x02_1*z131|
|x01_3|             |  x03_1  |  |  x03_1   |  |x03_1*z135|
|x01_4|             |  x04_1  |  |  x04_1   |  |x04_1*z139|
|x01_5|             |  x05_1  |  |  x05_1   |  |x05_1*z143|
|x01_6|             |  x06_1  |  |  x06_1   |  |x06_1*z147|
|x01_7|             |  x07_1  |  |  x07_1   |  |x07_1*z151|
|x02_0|             |  x00_2  |  |x00_2*z62 |  |  x00_2   |
|x02_1|             |  x01_2  |  |x01_2*z70 |  |  x01_2   |
|x02_2|             |  x02_2  |  |x02_2*z78 |  |  x02_2   |
|x02_3|             |  x03_2  |  |x03_2*z86 |  |  x03_2   |
|x02_4|             |  x04_2  |  |x04_2*z94 |  |  x04_2   |
|x02_5|             |  x05_2  |  |x05_2*z102|  |  x05_2   |
|x02_6|             |  x06_2  |  |x06_2*z110|  |  x06_2   |
|x02_7|             |  x07_2  |  |x07_2*z118|  |  x07_2   |
|x03_0|             |  x00_3  |  |x00_3*z62 |  |x00_3*z128|
|x03_1|             |  x01_3  |  |x01_3*z70 |  |x01_3*z132|
|x03_2|             |  x02_3  |  |x02_3*z78 |  |x02_3*z136|
|x03_3|             |  x03_3  |  |x03_3*z86 |  |x03_3*z140|
|x03_4|             |  x04_3  |  |x04_3*z94 |  |x04_3*z144|
|x03_5|             |  x05_3  |  |x05_3*z102|  |x05_3*z148|
|x03_6|             |  x06_3  |  |x06_3*z110|  |x06_3*z152|
|x03_7|             |  x07_3  |  |x07_3*z118|  |x07_3*z156|
         Transpose
|x04_0|             |x00_4*z31|  |  x00_4   |  |  x00_4   |
|x04_1|             |x01_4*z32|  |  x01_4   |  |  x01_4   |
|x04_2|             |x02_4*z33|  |  x02_4   |  |  x02_4   |
|x04_3|             |x03_4*z34|  |  x03_4   |  |  x03_4   |
|x04_4|             |x04_4*z35|  |  x04_4   |  |  x04_4   |
|x04_5|             |x05_4*z36|  |  x05_4   |  |  x05_4   |
|x04_6|             |x06_4*z37|  |  x06_4   |  |  x06_4   |
|x04_7|             |x07_4*z38|  |  x07_4   |  |  x07_4   |
|x05_0|             |x00_5*z31|  |  x00_5   |  |x00_5*z129|
|x05_1|             |x01_5*z32|  |  x01_5   |  |x01_5*z133|
|x05_2|             |x02_5*z33|  |  x02_5   |  |x02_5*z137|
|x05_3|             |x03_5*z34|  |  x03_5   |  |x03_5*z141|
|x05_4|             |x04_5*z35|  |  x04_5   |  |x04_5*z145|
|x05_5|             |x05_5*z36|  |  x05_5   |  |x05_5*z149|
|x05_6|             |x06_5*z37|  |  x06_5   |  |x06_5*z153|
|x05_7|             |x07_5*z38|  |  x07_5   |  |x07_5*z157|
|x06_0|             |x00_6*z31|  |x00_6*z63 |  |  x00_6   |
|x06_1|             |x01_6*z32|  |x01_6*z71 |  |  x01_6   |
|x06_2|             |x02_6*z33|  |x02_6*z79 |  |  x02_6   |
|x06_3|             |x03_6*z34|  |x03_6*z87 |  |  x03_6   |
|x06_4|             |x04_6*z35|  |x04_6*z95 |  |  x04_6   |
|x06_5|             |x05_6*z36|  |x05_6*z103|  |  x05_6   |
|x06_6|             |x06_6*z37|  |x06_6*z111|  |  x06_6   |
|x06_7|             |x07_6*z38|  |x07_6*z119|  |  x07_6   |
|x07_0|             |x00_7*z31|  |x00_7*z63 |  |x00_7*z130|
|x07_1|             |x01_7*z32|  |x01_7*z71 |  |x01_7*z134|
|x07_2|             |x02_7*z33|  |x02_7*z79 |  |x02_7*z138|
|x07_3|             |x03_7*z34|  |x03_7*z87 |  |x03_7*z142|
|x07_4|             |x04_7*z35|  |x04_7*z95 |  |x04_7*z146|
|x07_5|             |x05_7*z36|  |x05_7*z103|  |x05_7*z150|
|x07_6|             |x06_7*z37|  |x06_7*z111|  |x06_7*z154|
|x07_7|             |x07_7*z38|  |x07_7*z119|  |x07_7*z159|
   .                     .             .             .
   .                     .             .             .
   .                     .             .             .

[1] https://doi.org/10.46586/tches.v2022.i1.221-244
*/

/**
 * Compute the forward number-theoretic transform (NTT) for a polynomial f(x)
 * in Z_q / (X^256+1) where q < 2^24 in constant time. The resulting
 * coefficients are in bit-reversed ordering. The modulus q needs to be provided
 * in the MOD[31:0] register alongside the Montgomery constant
 * mu = -q^1 mod 2^32 in MOD[63:32].
 *
 * This routine can be in-place if x2 = x4.
 *
 * @param[in] x2: DMEM address of input polynomial (256 coefficients).
 * @param[out] x3: DMEM address of output polynomial (256 coefficients).
 */
ntt:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x4, x5, x6, x7, x8
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* In this routine, we will use w0-15 as the intermediate state holding the
     coefficients while w16 is used to hold an array of 8 twiddle factors. */
  li x5, 16

  /*
   * Layer 1:
   * The first layer is fully computed and store back into DMEM before the
   * subsequent layers.
   */

  /* Load the first array of 8 twiddle factors. Only the first element is
     used in the computation of the first layer. */
  la x4, _zeta
  bn.lid x5, 0(x4)

  /* Save the address registers for the input and output locations in DMEM. */
  addi x6, x2, 0
  addi x7, x3, 0

  /* Iteration 1: Coefficients 0-63 and 128-191.
     Iteration 2: Coefficients 64-127 and 192-255. */
  loopi 2, 44

    /* Load a batch of 128 coefficients. */
    addi x20, x6, 0
    addi x21, x0, 0
    jal  x1, _load_64x32
    addi x20, x20, 256
    jal  x1, _load_64x32

    bn.mulvml.8S w30,  w8, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w8,  w0, w30
    bn.addvm.8S   w0,  w0, w30
    bn.mulvml.8S w30,  w9, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w9,  w1, w30
    bn.addvm.8S   w1,  w1, w30
    bn.mulvml.8S w30, w10, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w10,  w2, w30
    bn.addvm.8S   w2,  w2, w30
    bn.mulvml.8S w30, w11, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w11,  w3, w30
    bn.addvm.8S   w3,  w3, w30
    bn.mulvml.8S w30, w12, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w12,  w4, w30
    bn.addvm.8S   w4,  w4, w30
    bn.mulvml.8S w30, w13, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w13,  w5, w30
    bn.addvm.8S   w5,  w5, w30
    bn.mulvml.8S w30, w14, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w14,  w6, w30
    bn.addvm.8S   w6,  w6, w30
    bn.mulvml.8S w30, w15, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w15,  w7, w30
    bn.addvm.8S   w7,  w7, w30

    /* Store back the transformed 128 coefficients. */
    addi x20, x7, 0
    addi x21, x0, 0
    jal  x1, _store_64x32
    addi x20, x20, 256
    jal  x1, _store_64x32

    /* Increment input and output DMEM addresses. */
    addi x6, x6, 256
    addi x7, x7, 256

    /* End of loop. */

  /* Set up input and twiddle DMEM address pointers. */
  addi x7, x3, 0
  addi x8, x4, 0

  /* Iteration 1: Coefficients 0-127.
     Iteration 2: Coefficients 128-255. */
  loopi 2, 251

    /*
     * Layer 2
     */
    bn.lid x5, 0(x8++)

    /* Reload the coefficients from DMEM and keep them in w0-16 until after
       the last Layer 8. */
    addi x20, x7, 0
    addi x21, x0, 0
    jal  x1, _load_64x32
    jal  x1, _load_64x32

    /* Iteration 1: zeta[1]
       Iteration 2: zeta[2] */
    bn.mulvml.8S w30,  w8, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w8,  w0, w30
    bn.addvm.8S   w0,  w0, w30
    bn.mulvml.8S w30,  w9, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w9,  w1, w30
    bn.addvm.8S   w1,  w1, w30
    bn.mulvml.8S w30, w10, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w10,  w2, w30
    bn.addvm.8S   w2,  w2, w30
    bn.mulvml.8S w30, w11, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w11,  w3, w30
    bn.addvm.8S   w3,  w3, w30
    bn.mulvml.8S w30, w12, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w12,  w4, w30
    bn.addvm.8S   w4,  w4, w30
    bn.mulvml.8S w30, w13, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w13,  w5, w30
    bn.addvm.8S   w5,  w5, w30
    bn.mulvml.8S w30, w14, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w14,  w6, w30
    bn.addvm.8S   w6,  w6, w30
    bn.mulvml.8S w30, w15, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w15,  w7, w30
    bn.addvm.8S   w7,  w7, w30

    /*
     * Layer 3
     */

    /* Iteration 1: zeta[3-4]
       Iteration 2: zeta[5-6] */
    bn.mulvml.8S w30,  w4, w16, 2
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w4,  w0, w30
    bn.addvm.8S   w0,  w0, w30
    bn.mulvml.8S w30,  w5, w16, 2
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w5,  w1, w30
    bn.addvm.8S   w1,  w1, w30
    bn.mulvml.8S w30,  w6, w16, 2
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w6,  w2, w30
    bn.addvm.8S   w2,  w2, w30
    bn.mulvml.8S w30,  w7, w16, 2
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w7,  w3, w30
    bn.addvm.8S   w3,  w3, w30
    bn.mulvml.8S w30, w12, w16, 3
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w12,  w8, w30
    bn.addvm.8S   w8,  w8, w30
    bn.mulvml.8S w30, w13, w16, 3
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w13,  w9, w30
    bn.addvm.8S   w9,  w9, w30
    bn.mulvml.8S w30, w14, w16, 3
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w14, w10, w30
    bn.addvm.8S  w10, w10, w30
    bn.mulvml.8S w30, w15, w16, 3
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w15, w11, w30
    bn.addvm.8S  w11, w11, w30

    /*
     * Layer 4
     */

    /* Iteration 1: zeta[7-10]
       Iteration 2: zeta[11-14] */
    bn.mulvml.8S w30,  w2, w16, 4
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w2,  w0, w30
    bn.addvm.8S   w0,  w0, w30
    bn.mulvml.8S w30,  w3, w16, 4
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w3,  w1, w30
    bn.addvm.8S   w1,  w1, w30
    bn.mulvml.8S w30,  w6, w16, 5
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w6,  w4, w30
    bn.addvm.8S   w4,  w4, w30
    bn.mulvml.8S w30,  w7, w16, 5
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w7,  w5, w30
    bn.addvm.8S   w5,  w5, w30
    bn.mulvml.8S w30, w10, w16, 6
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w10,  w8, w30
    bn.addvm.8S   w8,  w8, w30
    bn.mulvml.8S w30, w11, w16, 6
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w11,  w9, w30
    bn.addvm.8S   w9,  w9, w30
    bn.mulvml.8S w30, w14, w16, 7
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w14, w12, w30
    bn.addvm.8S  w12, w12, w30
    bn.mulvml.8S w30, w15, w16, 7
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w15, w13, w30
    bn.addvm.8S  w13, w13, w30

    /*
     * Layer 5
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[15-22]
       Iteration 2: zeta[23-30] */
    bn.mulvml.8S w30,  w1, w16, 0
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w1,  w0, w30
    bn.addvm.8S   w0,  w0, w30
    bn.mulvml.8S w30,  w3, w16, 1
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w3,  w2, w30
    bn.addvm.8S   w2,  w2, w30
    bn.mulvml.8S w30,  w5, w16, 2
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w5,  w4, w30
    bn.addvm.8S   w4,  w4, w30
    bn.mulvml.8S w30,  w7, w16, 3
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w7,  w6, w30
    bn.addvm.8S   w6,  w6, w30
    bn.mulvml.8S w30,  w9, w16, 4
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S   w9,  w8, w30
    bn.addvm.8S   w8,  w8, w30
    bn.mulvml.8S w30, w11, w16, 5
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w11, w10, w30
    bn.addvm.8S  w10, w10, w30
    bn.mulvml.8S w30, w13, w16, 6
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w13, w12, w30
    bn.addvm.8S  w12, w12, w30
    bn.mulvml.8S w30, w15, w16, 7
    bn.addvm.8S  w30, w30, w31 /* cond sub */
    bn.subvm.8S  w15, w14, w30
    bn.addvm.8S  w14, w14, w30

    /*
     * Layer 6
     */

    /* Transpose the 128 coefficients in w0-15. */
    jal x1, _transpose_8x8_w0w16

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[31-38]
       Iteration 2: zeta[47-54] */
    bn.mulvm.8S w30,  w4, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w4,  w0, w30
    bn.addvm.8S  w0,  w0, w30
    bn.mulvm.8S w30,  w5, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w5,  w1, w30
    bn.addvm.8S  w1,  w1, w30
    bn.mulvm.8S w30,  w6, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w6,  w2, w30
    bn.addvm.8S  w2,  w2, w30
    bn.mulvm.8S w30,  w7, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w7,  w3, w30
    bn.addvm.8S  w3,  w3, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[39-46]
       Iteration 2: zeta[55-62] */
    bn.mulvm.8S w30, w12, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w12,  w8, w30
    bn.addvm.8S  w8,  w8, w30
    bn.mulvm.8S w30, w13, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w13,  w9, w30
    bn.addvm.8S  w9,  w9, w30
    bn.mulvm.8S w30, w14, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w14, w10, w30
    bn.addvm.8S w10, w10, w30
    bn.mulvm.8S w30, w15, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w15, w11, w30
    bn.addvm.8S w11, w11, w30

    /*
     * Layer 7
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[63-70]
       Iteration 2: zeta[95-102] */
    bn.mulvm.8S w30,  w2, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w2,  w0, w30
    bn.addvm.8S  w0,  w0, w30
    bn.mulvm.8S w30,  w3, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w3,  w1, w30
    bn.addvm.8S  w1,  w1, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[71-78]
       Iteration 2: zeta[103-110] */
    bn.mulvm.8S w30,  w6, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w6,  w4, w30
    bn.addvm.8S  w4,  w4, w30
    bn.mulvm.8S w30,  w7, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w7,  w5, w30
    bn.addvm.8S  w5,  w5, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[79-86]
       Iteration 2: zeta[111-118] */
    bn.mulvm.8S w30, w10, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w10,  w8, w30
    bn.addvm.8S  w8,  w8, w30
    bn.mulvm.8S w30, w11, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w11,  w9, w30
    bn.addvm.8S  w9,  w9, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[87-94]
       Iteration 2: zeta[119-126] */
    bn.mulvm.8S w30, w14, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w14, w12, w30
    bn.addvm.8S w12, w12, w30
    bn.mulvm.8S w30, w15, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w15, w13, w30
    bn.addvm.8S w13, w13, w30

    /*
     * Layer 8
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[127-134]
       Iteration 2: zeta[192-199] */
    bn.mulvm.8S w30,  w1, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w1,  w0, w30
    bn.addvm.8S  w0,  w0, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[135-142]
       Iteration 2: zeta[200-207] */
    bn.mulvm.8S w30,  w3, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w3,  w2, w30
    bn.addvm.8S  w2,  w2, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[143-150]
       Iteration 2: zeta[208-215] */
    bn.mulvm.8S w30,  w5, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w5,  w4, w30
    bn.addvm.8S  w4,  w4, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[151-158]
       Iteration 2: zeta[216-223] */
    bn.mulvm.8S w30,  w7, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w7,  w6, w30
    bn.addvm.8S  w6,  w6, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[159-166]
       Iteration 2: zeta[224-231] */
    bn.mulvm.8S w30,  w9, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S  w9,  w8, w30
    bn.addvm.8S  w8,  w8, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[167-174]
       Iteration 2: zeta[232-239] */
    bn.mulvm.8S w30, w11, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w11, w10, w30
    bn.addvm.8S w10, w10, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[175-183]
       Iteration 2: zeta[240-247] */
    bn.mulvm.8S w30, w13, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w13, w12, w30
    bn.addvm.8S w12, w12, w30

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[184-191]
       Iteration 2: zeta[248-255] */
    bn.mulvm.8S w30, w15, w16
    bn.addvm.8S w30, w30, w31 /* cond sub */
    bn.subvm.8S w15, w14, w30
    bn.addvm.8S w14, w14, w30

    /* Transpose w0-w15 back before storing it in the output buffer. */
    jal x1, _transpose_8x8_w0w16

    addi x20, x7, 0
    addi x21, x0, 0
    jal  x1, _store_64x32
    jal  x1, _store_64x32

    /* Move the output DMEM pointer to the second half of the array. */
    addi x7, x7, 512
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x8, x7, x6, x5, x4
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Compute the backward number-theoretic transform (NTT) for a polynomial f(x)
 * in Z_q / (X^256+1) where q < 2^24 in constant time. The resulting
 * coefficients are in bit-reversed ordering. The modulus q needs to be provided
 * in the MOD[31:0] register alongside the Montgomery constant
 * mu = -q^1 mod 2^32 in MOD[63:32].
 *
 * This routine can be in-place if x2 = x4.
 *
 * @param[in] x2: DMEM address of input polynomial (256 coefficients).
 * @param[out] x3: DMEM address of output polynomial (256 coefficients).
 */
intt:
  /* Push clobbered general-purpose registers onto the stack. */
  .irp reg, x4, x5, x6, x7, x8
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* In this routine, we will use w0-15 as the intermediate state holding the
     coefficients while w16 is used to hold an array of 8 twiddle factors. */
  li x5, 16

  /*
   * Layer 1
   */

  /* Set up DMEM address pointers. */
  la x4, _zeta_inv
  addi x6, x2, 0
  addi x7, x3, 0
  addi x8, x4, 0

  /* Iteration 1: Coefficients 0-127.
     Iteration 2: Coefficients 128-255. */
  loopi 2, 252

    addi x20, x6, 0
    addi x21, x0, 0
    jal  x1, _load_64x32
    jal  x1, _load_64x32

    jal x1, _transpose_8x8_w0w16

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[127-134]
       Iteration 2: zeta[192-199] */
    bn.subvm.8S w30,  w0,  w1
    bn.addvm.8S  w0,  w0,  w1
    bn.mulvm.8S  w1, w30, w16
    bn.addvm.8S  w1,  w1, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[135-142]
       Iteration 2: zeta[200-207] */
    bn.subvm.8S w30,  w2,  w3
    bn.addvm.8S  w2,  w2,  w3
    bn.mulvm.8S  w3, w30, w16
    bn.addvm.8S  w3,  w3, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[143-150]
       Iteration 2: zeta[208-215] */
    bn.subvm.8S w30,  w4,  w5
    bn.addvm.8S  w4,  w4,  w5
    bn.mulvm.8S  w5, w30, w16
    bn.addvm.8S  w5,  w5, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[151-158]
       Iteration 2: zeta[216-223] */
    bn.subvm.8S w30,  w6,  w7
    bn.addvm.8S  w6,  w6,  w7
    bn.mulvm.8S  w7, w30, w16
    bn.addvm.8S  w7,  w7, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[159-166]
       Iteration 2: zeta[224-231] */
    bn.subvm.8S w30,  w8,  w9
    bn.addvm.8S  w8,  w8,  w9
    bn.mulvm.8S  w9, w30, w16
    bn.addvm.8S  w9,  w9, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[167-174]
       Iteration 2: zeta[232-239] */
    bn.subvm.8S w30, w10, w11
    bn.addvm.8S w10, w10, w11
    bn.mulvm.8S w11, w30, w16
    bn.addvm.8S w11, w11, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[175-183]
       Iteration 2: zeta[240-247] */
    bn.subvm.8S w30, w12, w13
    bn.addvm.8S w12, w12, w13
    bn.mulvm.8S w13, w30, w16
    bn.addvm.8S w13, w13, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[184-191]
       Iteration 2: zeta[248-255] */
    bn.subvm.8S w30, w14, w15
    bn.addvm.8S w14, w14, w15
    bn.mulvm.8S w15, w30, w16
    bn.addvm.8S w15, w15, w31 /* cond sub */

    /*
     * Layer 2
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[63-70]
       Iteration 2: zeta[95-102] */
    bn.subvm.8S w30,  w0,  w2
    bn.addvm.8S  w0,  w0,  w2
    bn.mulvm.8S  w2, w30, w16
    bn.addvm.8S  w2,  w2, w31 /* cond sub */
    bn.subvm.8S w30,  w1,  w3
    bn.addvm.8S  w1,  w1,  w3
    bn.mulvm.8S  w3, w30, w16
    bn.addvm.8S  w3,  w3, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[71-78]
       Iteration 2: zeta[103-110] */
    bn.subvm.8S w30,  w4,  w6
    bn.addvm.8S  w4,  w4,  w6
    bn.mulvm.8S  w6, w30, w16
    bn.addvm.8S  w6,  w6, w31 /* cond sub */
    bn.subvm.8S w30,  w5,  w7
    bn.addvm.8S  w5,  w5,  w7
    bn.mulvm.8S  w7, w30, w16
    bn.addvm.8S  w7,  w7, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[79-86]
       Iteration 2: zeta[111-118] */
    bn.subvm.8S w30,  w8, w10
    bn.addvm.8S  w8,  w8, w10
    bn.mulvm.8S w10, w30, w16
    bn.addvm.8S w10, w10, w31 /* cond sub */
    bn.subvm.8S w30,  w9, w11
    bn.addvm.8S  w9,  w9, w11
    bn.mulvm.8S w11, w30, w16
    bn.addvm.8S w11, w11, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[87-94]
       Iteration 2: zeta[119-126] */
    bn.subvm.8S w30, w12, w14
    bn.addvm.8S w12, w12, w14
    bn.mulvm.8S w14, w30, w16
    bn.addvm.8S w14, w14, w31 /* cond sub */
    bn.subvm.8S w30, w13, w15
    bn.addvm.8S w13, w13, w15
    bn.mulvm.8S w15, w30, w16
    bn.addvm.8S w15, w15, w31 /* cond sub */

    /*
     * Layer 3
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[31-38]
       Iteration 2: zeta[47-54] */
    bn.subvm.8S w30,  w0,  w4
    bn.addvm.8S  w0,  w0,  w4
    bn.mulvm.8S  w4, w30, w16
    bn.addvm.8S  w4,  w4, w31 /* cond sub */
    bn.subvm.8S w30,  w1,  w5
    bn.addvm.8S  w1,  w1,  w5
    bn.mulvm.8S  w5, w30, w16
    bn.addvm.8S  w5,  w5, w31 /* cond sub */
    bn.subvm.8S w30,  w2,  w6
    bn.addvm.8S  w2,  w2,  w6
    bn.mulvm.8S  w6, w30, w16
    bn.addvm.8S  w6,  w6, w31 /* cond sub */
    bn.subvm.8S w30,  w3,  w7
    bn.addvm.8S  w3,  w3,  w7
    bn.mulvm.8S  w7, w30, w16
    bn.addvm.8S  w7,  w7, w31 /* cond sub */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[39-46]
       Iteration 2: zeta[55-62] */
    bn.subvm.8S w30,  w8, w12
    bn.addvm.8S  w8,  w8, w12
    bn.mulvm.8S w12, w30, w16
    bn.addvm.8S w12, w12, w31 /* cond sub */
    bn.subvm.8S w30,  w9, w13
    bn.addvm.8S  w9,  w9, w13
    bn.mulvm.8S w13, w30, w16
    bn.addvm.8S w13, w13, w31 /* cond sub */
    bn.subvm.8S w30, w10, w14
    bn.addvm.8S w10, w10, w14
    bn.mulvm.8S w14, w30, w16
    bn.addvm.8S w14, w14, w31 /* cond sub */
    bn.subvm.8S w30, w11, w15
    bn.addvm.8S w11, w11, w15
    bn.mulvm.8S w15, w30, w16
    bn.addvm.8S w15, w15, w31 /* cond sub */

    /* Transpose w0-w15 back before storing it in the output buffer. */
    jal x1, _transpose_8x8_w0w16

    /*
     * Layer 4
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[15-22]
       Iteration 2: zeta[23-30] */
    bn.subvm.8S  w30,  w0,  w1
    bn.addvm.8S   w0,  w0,  w1
    bn.mulvml.8S  w1, w30, w16, 0
    bn.addvm.8S   w1,  w1, w31 /* cond sub */
    bn.subvm.8S  w30,  w2,  w3
    bn.addvm.8S   w2,  w2,  w3
    bn.mulvml.8S  w3, w30, w16, 1
    bn.addvm.8S   w3,  w3, w31 /* cond sub */
    bn.subvm.8S  w30,  w4,  w5
    bn.addvm.8S   w4,  w4,  w5
    bn.mulvml.8S  w5, w30, w16, 2
    bn.addvm.8S   w5,  w5, w31 /* cond sub */
    bn.subvm.8S  w30,  w6,  w7
    bn.addvm.8S   w6,  w6,  w7
    bn.mulvml.8S  w7, w30, w16, 3
    bn.addvm.8S   w7,  w7, w31 /* cond sub */
    bn.subvm.8S  w30,  w8,  w9
    bn.addvm.8S   w8,  w8,  w9
    bn.mulvml.8S  w9, w30, w16, 4
    bn.addvm.8S   w9,  w9, w31 /* cond sub */
    bn.subvm.8S  w30, w10, w11
    bn.addvm.8S  w10, w10, w11
    bn.mulvml.8S w11, w30, w16, 5
    bn.addvm.8S  w11, w11, w31 /* cond sub */
    bn.subvm.8S  w30, w12, w13
    bn.addvm.8S  w12, w12, w13
    bn.mulvml.8S w13, w30, w16, 6
    bn.addvm.8S  w13, w13, w31 /* cond sub */
    bn.subvm.8S  w30, w14, w15
    bn.addvm.8S  w14, w14, w15
    bn.mulvml.8S w15, w30, w16, 7
    bn.addvm.8S  w15, w15, w31 /* cond sub */

    /*
     * Layer 5
     */

    bn.lid x5, 0(x8++)

    /* Iteration 1: zeta[7-10]
       Iteration 2: zeta[11-14] */
    bn.subvm.8S  w30,  w0,  w2
    bn.addvm.8S   w0,  w0,  w2
    bn.mulvml.8S  w2, w30, w16, 0
    bn.addvm.8S   w2,  w2, w31 /* cond sub */
    bn.subvm.8S  w30,  w1,  w3
    bn.addvm.8S   w1,  w1,  w3
    bn.mulvml.8S  w3, w30, w16, 0
    bn.addvm.8S   w3,  w3, w31 /* cond sub */
    bn.subvm.8S  w30,  w4,  w6
    bn.addvm.8S   w4,  w4,  w6
    bn.mulvml.8S  w6, w30, w16, 1
    bn.addvm.8S   w6,  w6, w31 /* cond sub */
    bn.subvm.8S  w30,  w5,  w7
    bn.addvm.8S   w5,  w5,  w7
    bn.mulvml.8S  w7, w30, w16, 1
    bn.addvm.8S   w7,  w7, w31 /* cond sub */
    bn.subvm.8S  w30,  w8, w10
    bn.addvm.8S   w8,  w8, w10
    bn.mulvml.8S w10, w30, w16, 2
    bn.addvm.8S  w10, w10, w31 /* cond sub */
    bn.subvm.8S  w30,  w9, w11
    bn.addvm.8S   w9,  w9, w11
    bn.mulvml.8S w11, w30, w16, 2
    bn.addvm.8S  w11, w11, w31 /* cond sub */
    bn.subvm.8S  w30, w12, w14
    bn.addvm.8S  w12, w12, w14
    bn.mulvml.8S w14, w30, w16, 3
    bn.addvm.8S  w14, w14, w31 /* cond sub */
    bn.subvm.8S  w30, w13, w15
    bn.addvm.8S  w13, w13, w15
    bn.mulvml.8S w15, w30, w16, 3
    bn.addvm.8S  w15, w15, w31 /* cond sub */

    /*
     * Layer 6
     */

    /* Iteration 1: zeta[3-4]
       Iteration 2: zeta[5-6] */
    bn.subvm.8S  w30,  w0,  w4
    bn.addvm.8S   w0,  w0,  w4
    bn.mulvml.8S  w4, w30, w16, 4
    bn.addvm.8S   w4,  w4, w31 /* cond sub */
    bn.subvm.8S  w30,  w1,  w5
    bn.addvm.8S   w1,  w1,  w5
    bn.mulvml.8S  w5, w30, w16, 4
    bn.addvm.8S   w5,  w5, w31 /* cond sub */
    bn.subvm.8S  w30,  w2,  w6
    bn.addvm.8S   w2,  w2,  w6
    bn.mulvml.8S  w6, w30, w16, 4
    bn.addvm.8S   w6,  w6, w31 /* cond sub */
    bn.subvm.8S  w30,  w3,  w7
    bn.addvm.8S   w3,  w3,  w7
    bn.mulvml.8S  w7, w30, w16, 4
    bn.addvm.8S   w7,  w7, w31 /* cond sub */
    bn.subvm.8S  w30,  w8, w12
    bn.addvm.8S   w8,  w8, w12
    bn.mulvml.8S w12, w30, w16, 5
    bn.addvm.8S  w12, w12, w31 /* cond sub */
    bn.subvm.8S  w30,  w9, w13
    bn.addvm.8S   w9,  w9, w13
    bn.mulvml.8S w13, w30, w16, 5
    bn.addvm.8S  w13, w13, w31 /* cond sub */
    bn.subvm.8S  w30, w10, w14
    bn.addvm.8S  w10, w10, w14
    bn.mulvml.8S w14, w30, w16, 5
    bn.addvm.8S  w14, w14, w31 /* cond sub */
    bn.subvm.8S  w30, w11, w15
    bn.addvm.8S  w11, w11, w15
    bn.mulvml.8S w15, w30, w16, 5
    bn.addvm.8S  w15, w15, w31 /* cond sub */

    /*
     * Layer 7
     */

    /* Iteration 1: zeta[1]
       Iteration 2: zeta[2] */
    bn.subvm.8S  w30,  w0,  w8
    bn.addvm.8S   w0,  w0,  w8
    bn.mulvml.8S  w8, w30, w16, 6
    bn.addvm.8S   w8,  w8, w31 /* cond sub */
    bn.subvm.8S  w30,  w1,  w9
    bn.addvm.8S   w1,  w1,  w9
    bn.mulvml.8S  w9, w30, w16, 6
    bn.addvm.8S   w9,  w9, w31 /* cond sub */
    bn.subvm.8S  w30,  w2, w10
    bn.addvm.8S   w2,  w2, w10
    bn.mulvml.8S w10, w30, w16, 6
    bn.addvm.8S  w10, w10, w31 /* cond sub */
    bn.subvm.8S  w30,  w3, w11
    bn.addvm.8S   w3,  w3, w11
    bn.mulvml.8S w11, w30, w16, 6
    bn.addvm.8S  w11, w11, w31 /* cond sub */
    bn.subvm.8S  w30,  w4, w12
    bn.addvm.8S   w4,  w4, w12
    bn.mulvml.8S w12, w30, w16, 6
    bn.addvm.8S  w12, w12, w31 /* cond sub */
    bn.subvm.8S  w30,  w5, w13
    bn.addvm.8S   w5,  w5, w13
    bn.mulvml.8S w13, w30, w16, 6
    bn.addvm.8S  w13, w13, w31 /* cond sub */
    bn.subvm.8S  w30,  w6, w14
    bn.addvm.8S   w6,  w6, w14
    bn.mulvml.8S w14, w30, w16, 6
    bn.addvm.8S  w14, w14, w31 /* cond sub */
    bn.subvm.8S  w30,  w7, w15
    bn.addvm.8S   w7,  w7, w15
    bn.mulvml.8S w15, w30, w16, 6
    bn.addvm.8S  w15, w15, w31 /* cond sub */

    /* Store back the transformed 128 coefficients. */
    addi x20, x7, 0
    addi x21, x0, 0
    jal  x1, _store_64x32
    jal  x1, _store_64x32

    /* Move the DMEM pointers to the second halves of the arrays. */
    addi x6, x6, 512
    addi x7, x7, 512
    /* End of loop */

  /*
   * Layer 8
   */

  addi x6, x3, 0

  /* Load 256^-1 mod q into w17 */
  bn.wsrr w17, MOD
  bn.rshi w17, w31, w17 >> 64

  /* Iteration 1: Coefficients 0-63 and 128-191.
     Iteration 2: Coefficients 64-127 and 192-255. */
  loopi 2, 75

    /* Load a batch of 128 coefficients. */
    addi x20, x6, 0
    addi x21, x0, 0
    jal  x1, _load_64x32
    addi x20, x20, 256
    jal  x1, _load_64x32

    bn.subvm.8S  w30,  w0,  w8
    bn.addvm.8S   w0,  w0,  w8
    bn.mulvml.8S  w8, w30, w16, 7
    bn.addvm.8S   w8,  w8, w31  /* cond sub */
    bn.subvm.8S  w30,  w1,  w9
    bn.addvm.8S   w1,  w1,  w9
    bn.mulvml.8S  w9, w30, w16, 7
    bn.addvm.8S   w9,  w9, w31 /* cond sub */
    bn.subvm.8S  w30,  w2, w10
    bn.addvm.8S   w2,  w2, w10
    bn.mulvml.8S w10, w30, w16, 7
    bn.addvm.8S  w10, w10, w31 /* cond sub */
    bn.subvm.8S  w30,  w3, w11
    bn.addvm.8S   w3,  w3, w11
    bn.mulvml.8S w11, w30, w16, 7
    bn.addvm.8S  w11, w11, w31 /* cond sub */
    bn.subvm.8S  w30,  w4, w12
    bn.addvm.8S   w4,  w4, w12
    bn.mulvml.8S w12, w30, w16, 7
    bn.addvm.8S  w12, w12, w31 /* cond sub */
    bn.subvm.8S  w30,  w5, w13
    bn.addvm.8S   w5,  w5, w13
    bn.mulvml.8S w13, w30, w16, 7
    bn.addvm.8S  w13, w13, w31 /* cond sub */
    bn.subvm.8S  w30,  w6, w14
    bn.addvm.8S   w6,  w6, w14
    bn.mulvml.8S w14, w30, w16, 7
    bn.addvm.8S  w14, w14, w31 /* cond sub */
    bn.subvm.8S  w30,  w7, w15
    bn.addvm.8S   w7,  w7, w15
    bn.mulvml.8S w15, w30, w16, 7
    bn.addvm.8S  w15, w15, w31 /* cond sub */

    /* Multiply the coefficients by 256^-1 mod q. */
    bn.mulvml.8S  w0,  w0, w17, 0
    bn.mulvml.8S  w1,  w1, w17, 0
    bn.mulvml.8S  w2,  w2, w17, 0
    bn.mulvml.8S  w3,  w3, w17, 0
    bn.mulvml.8S  w4,  w4, w17, 0
    bn.mulvml.8S  w5,  w5, w17, 0
    bn.mulvml.8S  w6,  w6, w17, 0
    bn.mulvml.8S  w7,  w7, w17, 0
    bn.mulvml.8S  w8,  w8, w17, 0
    bn.mulvml.8S  w9,  w9, w17, 0
    bn.mulvml.8S w10, w10, w17, 0
    bn.mulvml.8S w11, w11, w17, 0
    bn.mulvml.8S w12, w12, w17, 0
    bn.mulvml.8S w13, w13, w17, 0
    bn.mulvml.8S w14, w14, w17, 0
    bn.mulvml.8S w15, w15, w17, 0

    bn.addvm.8S  w0,  w0, w31
    bn.addvm.8S  w1,  w1, w31
    bn.addvm.8S  w2,  w2, w31
    bn.addvm.8S  w3,  w3, w31
    bn.addvm.8S  w4,  w4, w31
    bn.addvm.8S  w5,  w5, w31
    bn.addvm.8S  w6,  w6, w31
    bn.addvm.8S  w7,  w7, w31
    bn.addvm.8S  w8,  w8, w31
    bn.addvm.8S  w9,  w9, w31
    bn.addvm.8S w10, w10, w31
    bn.addvm.8S w11, w11, w31
    bn.addvm.8S w12, w12, w31
    bn.addvm.8S w13, w13, w31
    bn.addvm.8S w14, w14, w31
    bn.addvm.8S w15, w15, w31

    /* Store back the transformed 128 coefficients. */
    addi x20, x6, 0
    addi x21, x0, 0
    jal  x1, _store_64x32
    addi x20, x20, 256
    jal  x1, _store_64x32

    /* Increment output DMEM address. */
    addi x6, x6, 256
    /* End of loop. */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x8, x7, x6, x5, x4
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/* The reduce the clutter in *_mem and test files declare the twiddle factors
   here. Make sure that these are not placed at the end of the .data section in
   the ELF file to guarantee that correct placement of the stack. */
.data
.balign 32

/* ML-DSA twiddle factors (zeta) in bit-reversed ordering and in the Montgomery
   domain partitioned into two halves (lower and upper 128 coefficients).

   tmp[i] = w^(bit_rev(i)) * R^2 mod q. for i in [0, 256)
   for i in [1, 2, 4, 8, 16, 32, 64, 128]:
     for j in [i, i+i/2]:   zeta[j] = tmp[j] # Half 1
     for j in [i+i/2, 2*i]: zeta[j] = tmp[j] # Half 2 */
_zeta:

/*
 * Half 1
 */

/* Layer 1 */
.word 0x000064f7
/* Layer 2 */
.word 0x00581103
/* Layer 3 */
.word 0x00039e44
.word 0x00740119
/* Layer 4 */
.word 0x001bde2b
.word 0x0023e92b
.word 0x007a64ae
.word 0x005ff480
/* Layer 5 */
.word 0x00299658
.word 0x000fa070
.word 0x006f65a5
.word 0x0036b788
.word 0x00777d91
.word 0x006ecaa1
.word 0x0027f968
.word 0x005fb37c
/* Layer 6 */
.word 0x00294a67
.word 0x00017620
.word 0x002ef4cd
.word 0x0035dec5
.word 0x00668504
.word 0x0049102d
.word 0x005927d5
.word 0x003bbeaf
.word 0x0044f586
.word 0x00516e7d
.word 0x00368a96
.word 0x00541e42
.word 0x00360400
.word 0x007b4a4e
.word 0x0023d69c
.word 0x0077a55e
/* Layer 7 (8x1 transposed) */
.word 0x0043e6e6 /* 0x0043e6e6 (untransposed) */
.word 0x0047c1d0 /* 0x00688c82 */
.word 0x0069b65e /* 0x0047c1d0 */
.word 0x002135c7 /* 0x0051781a */
.word 0x006caf76 /* 0x0069b65e */
.word 0x00419073 /* 0x003509ee */
.word 0x004f3281 /* 0x002135c7 */
.word 0x004870e1 /* 0x0067afbc */
.word 0x00688c82 /* 0x006caf76 */
.word 0x0051781a /* 0x001d9772 */
.word 0x003509ee /* 0x00419073 */
.word 0x0067afbc /* 0x00709cf7 */
.word 0x001d9772 /* 0x004f3281 */
.word 0x00709cf7 /* 0x004fb2af */
.word 0x004fb2af /* 0x004870e1 */
.word 0x0001efca /* 0x0001efca */
.word 0x003410f2 /* 0x003410f2 */
.word 0x0020c638 /* 0x0070de86 */
.word 0x005297a4 /* 0x0020c638 */
.word 0x00799a6e /* 0x00296e9f */
.word 0x0075a283 /* 0x005297a4 */
.word 0x007f863c /* 0x0047844c */
.word 0x007a0bde /* 0x00799a6e */
.word 0x001c4563 /* 0x005a140a */
.word 0x0070de86 /* 0x0075a283 */
.word 0x00296e9f /* 0x006d2114 */
.word 0x0047844c /* 0x007f863c */
.word 0x005a140a /* 0x006be9f8 */
.word 0x006d2114 /* 0x007a0bde */
.word 0x006be9f8 /* 0x001495d4 */
.word 0x001495d4 /* 0x001c4563 */
.word 0x006a0c63 /* 0x006a0c63 */
/* Layer 8 (4x1 transposed) */
.word 0x001fea93 /* 0x001fea93 (untransposed) */
.word 0x004cdf73 /* 0x0033ff5a */
.word 0x000412f5 /* 0x002358d4 */
.word 0x004a28a1 /* 0x003a41f8 */
.word 0x000dbe5e /* 0x004cdf73 */
.word 0x00078f83 /* 0x00223dfb */
.word 0x0075e022 /* 0x005a8ba0 */
.word 0x0049997e /* 0x00498423 */
.word 0x0033ff5a /* 0x000412f5 */
.word 0x00223dfb /* 0x00252587 */
.word 0x00252587 /* 0x006d04f1 */
.word 0x004682fd /* 0x00359b5d */
.word 0x001c5e1a /* 0x004a28a1 */
.word 0x0067428b /* 0x004682fd */
.word 0x00503af7 /* 0x006d9b57 */
.word 0x0077dcd7 /* 0x004f25df */
.word 0x002358d4 /* 0x000dbe5e */
.word 0x005a8ba0 /* 0x001c5e1a */
.word 0x006d04f1 /* 0x000de0e6 */
.word 0x006d9b57 /* 0x000c7f5a */
.word 0x000de0e6 /* 0x00078f83 */
.word 0x007f3705 /* 0x0067428b */
.word 0x001f0084 /* 0x007f3705 */
.word 0x00742593 /* 0x0077e6fd */
.word 0x003a41f8 /* 0x0075e022 */
.word 0x00498423 /* 0x00503af7 */
.word 0x00359b5d /* 0x001f0084 */
.word 0x004f25df /* 0x0030ef86 */
.word 0x000c7f5a /* 0x0049997e */
.word 0x0077e6fd /* 0x0077dcd7 */
.word 0x0030ef86 /* 0x00742593 */
.word 0x004901c3 /* 0x004901c3 */
.word 0x00053919 /* 0x00053919 */
.word 0x003472e7 /* 0x0004610c */
.word 0x002b5ee5 /* 0x005aad42 */
.word 0x003de11c /* 0x003eb01b */
.word 0x00466519 /* 0x003472e7 */
.word 0x0052308a /* 0x004ce03c */
.word 0x006b88bf /* 0x001a7cc7 */
.word 0x0078fde5 /* 0x00031924 */
.word 0x0004610c /* 0x002b5ee5 */
.word 0x004ce03c /* 0x00291199 */
.word 0x00291199 /* 0x00585a3b */
.word 0x00130984 /* 0x00134d71 */
.word 0x001314be /* 0x003de11c */
.word 0x001c853f /* 0x00130984 */
.word 0x0012e11b /* 0x0025f051 */
.word 0x001406c7 /* 0x00185a46 */
.word 0x005aad42 /* 0x00466519 */
.word 0x001a7cc7 /* 0x001314be */
.word 0x00585a3b /* 0x00283891 */
.word 0x0025f051 /* 0x0049bb91 */
.word 0x00283891 /* 0x0052308a */
.word 0x001d0b4b /* 0x001c853f */
.word 0x004d3e3f /* 0x001d0b4b */
.word 0x00327283 /* 0x006fd6a7 */
.word 0x003eb01b /* 0x006b88bf */
.word 0x00031924 /* 0x0012e11b */
.word 0x00134d71 /* 0x004d3e3f */
.word 0x00185a46 /* 0x006a0d30 */
.word 0x0049bb91 /* 0x0078fde5 */
.word 0x006fd6a7 /* 0x001406c7 */
.word 0x006a0d30 /* 0x00327283 */
.word 0x0061ed6f /* 0x0061ed6f */

/*
 * Half 2
 */

/* Layer 1 (unused) */
.word 0x00000000
/* Layer 2 */
.word 0x0077f504
/* Layer 3 */
.word 0x00728129
.word 0x00071e24
/* Layer 4 */
.word 0x002f9a75
.word 0x0053db0a
.word 0x002f7a49
.word 0x0028e527
/* Layer 5 */
.word 0x005f8dd7
.word 0x0044fae8
.word 0x006a84f8
.word 0x004ddc99
.word 0x001ad035
.word 0x007f9423
.word 0x003d3201
.word 0x000445c5
/* Layer 6 */
.word 0x0065f23e
.word 0x0066cad7
.word 0x00357e1e
.word 0x00458f5a
.word 0x0035843f
.word 0x005f3618
.word 0x0067745d
.word 0x0038738c
.word 0x000c63a8
.word 0x00081b9a
.word 0x000e8f76
.word 0x003b3853
.word 0x003b8534
.word 0x0058dc31
.word 0x001f9d54
.word 0x00552f2e
/* Layer 7 (8x1 transposed) */
.word 0x004cdbea /* 0x004cdbea (untransposed) */
.word 0x0007c417 /* 0x00040af0 */
.word 0x0000ad00 /* 0x0007c417 */
.word 0x000dcd44 /* 0x002f4588 */
.word 0x00470bcb /* 0x0000ad00 */
.word 0x00193948 /* 0x006f16bf */
.word 0x0024756c /* 0x000dcd44 */
.word 0x000b98a1 /* 0x003c675a */
.word 0x00040af0 /* 0x00470bcb */
.word 0x002f4588 /* 0x007fbe7f */
.word 0x006f16bf /* 0x00193948 */
.word 0x003c675a /* 0x004e49c1 */
.word 0x007fbe7f /* 0x0024756c */
.word 0x004e49c1 /* 0x007ca7e0 */
.word 0x007ca7e0 /* 0x000b98a1 */
.word 0x006bc809 /* 0x006bc809 */
.word 0x0002e46c /* 0x0002e46c */
.word 0x003036c2 /* 0x0049a809 */
.word 0x005b1c94 /* 0x003036c2 */
.word 0x00141305 /* 0x00639ff7 */
.word 0x00139e25 /* 0x005b1c94 */
.word 0x00737945 /* 0x007d2ae1 */
.word 0x0051cea3 /* 0x00141305 */
.word 0x00488058 /* 0x00147792 */
.word 0x0049a809 /* 0x00139e25 */
.word 0x00639ff7 /* 0x0067b0e1 */
.word 0x007d2ae1 /* 0x00737945 */
.word 0x00147792 /* 0x0069e803 */
.word 0x0067b0e1 /* 0x0051cea3 */
.word 0x0069e803 /* 0x0044a79d */
.word 0x0044a79d /* 0x00488058 */
.word 0x003a97d9 /* 0x003a97d9 */
/* Layer 8 (4x1 transposed) */
.word 0x006c5954 /* 0x006c5954 (untransposed) */
.word 0x0016e405 /* 0x001d4099 */
.word 0x00779935 /* 0x00590579 */
.word 0x0058711c /* 0x006ae5ae */
.word 0x00612659 /* 0x0016e405 */
.word 0x001ddd98 /* 0x000bdbe7 */
.word 0x004f4cbf /* 0x00221de8 */
.word 0x000c5ca5 /* 0x0033f8cf */
.word 0x001d4099 /* 0x00779935 */
.word 0x000bdbe7 /* 0x0054aa0d */
.word 0x0054aa0d /* 0x00665ff9 */
.word 0x00470c13 /* 0x0063b158 */
.word 0x00251d8b /* 0x0058711c */
.word 0x00336898 /* 0x00470c13 */
.word 0x00027c1c /* 0x000910d8 */
.word 0x0019379a /* 0x00463e20 */
.word 0x00590579 /* 0x00612659 */
.word 0x00221de8 /* 0x00251d8b */
.word 0x00665ff9 /* 0x002573b7 */
.word 0x000910d8 /* 0x007d5c90 */
.word 0x002573b7 /* 0x001ddd98 */
.word 0x0002d4bb /* 0x00336898 */
.word 0x0018aa08 /* 0x0002d4bb */
.word 0x00478168 /* 0x006d73a8 */
.word 0x006ae5ae /* 0x004f4cbf */
.word 0x0033f8cf /* 0x00027c1c */
.word 0x0063b158 /* 0x0018aa08 */
.word 0x00463e20 /* 0x002dfd71 */
.word 0x007d5c90 /* 0x000c5ca5 */
.word 0x006d73a8 /* 0x0019379a */
.word 0x002dfd71 /* 0x00478168 */
.word 0x00646c3e /* 0x00646c3e */
.word 0x0051813d /* 0x0051813d */
.word 0x0021c4f7 /* 0x0035c539 */
.word 0x00795d46 /* 0x003b0115 */
.word 0x00666e99 /* 0x00041dc0 */
.word 0x00530765 /* 0x0021c4f7 */
.word 0x0002cc93 /* 0x0070fbf5 */
.word 0x00776a51 /* 0x001a35e7 */
.word 0x003c15ca /* 0x0007340e */
.word 0x0035c539 /* 0x00795d46 */
.word 0x0070fbf5 /* 0x001a4cd0 */
.word 0x001a4cd0 /* 0x00645caf */
.word 0x006f0634 /* 0x001d2668 */
.word 0x005dc1b0 /* 0x00666e99 */
.word 0x0070f806 /* 0x006f0634 */
.word 0x003bcf2c /* 0x007be5db */
.word 0x00155e68 /* 0x00455fdc */
.word 0x003b0115 /* 0x00530765 */
.word 0x001a35e7 /* 0x005dc1b0 */
.word 0x00645caf /* 0x007973de */
.word 0x007be5db /* 0x005cfd0a */
.word 0x007973de /* 0x0002cc93 */
.word 0x00189c2a /* 0x0070f806 */
.word 0x007f234f /* 0x00189c2a */
.word 0x0072f6b7 /* 0x0049c5aa */
.word 0x00041dc0 /* 0x00776a51 */
.word 0x0007340e /* 0x003bcf2c */
.word 0x001d2668 /* 0x007f234f */
.word 0x00455fdc /* 0x006b16e0 */
.word 0x005cfd0a /* 0x003c15ca */
.word 0x0049c5aa /* 0x00155e68 */
.word 0x006b16e0 /* 0x0072f6b7 */
.word 0x001e29ce /* 0x001e29ce */

/* ML-DSA inverse twiddle factors (zeta) in bit-reversed ordering and in the
   Montgomery domain partitioned into two halves (lower and upper 128
   coefficients). The factors are stored in unpacked form (256 32-bit elements).
   Stored here instead of a testcase file for better inspection.

   tmp[i] = w^(bit_rev(i)) * R^2 mod q. for i in [0, 256)
   for i in [128, 64, 32, 16, 8, 4, 2, 1]:
     for j in [i+i/2, 2*i]: zeta[2*i-j]     = -tmp[j] % q # Half 1
     for j in [i, i+i/2]:   zeta[(i+i/2)-j] = -tmp[j] % q # Half 2 */
_zeta_inv:

/*
 * Half 1
 */

/* Layer 8 (4x1 transposed) */
.word 0x0061b633 /* 0x0061b633 (untransposed) */
.word 0x0014c921 /* 0x000ce94a */
.word 0x00361a57 /* 0x006a8199 */
.word 0x0022e2f7 /* 0x0043ca37 */
.word 0x003a8025 /* 0x0014c921 */
.word 0x0062b999 /* 0x0000bcb2 */
.word 0x0078abf3 /* 0x004410d5 */
.word 0x007bc241 /* 0x000875b0 */
.word 0x000ce94a /* 0x00361a57 */
.word 0x0000bcb2 /* 0x006743d7 */
.word 0x006743d7 /* 0x000ee7fb */
.word 0x00066c23 /* 0x007d136e */
.word 0x0003fa26 /* 0x0022e2f7 */
.word 0x001b8352 /* 0x00066c23 */
.word 0x0065aa1a /* 0x00221e51 */
.word 0x0044deec /* 0x002cd89c */
.word 0x006a8199 /* 0x003a8025 */
.word 0x004410d5 /* 0x0003fa26 */
.word 0x000ee7fb /* 0x0010d9cd */
.word 0x00221e51 /* 0x00197168 */
.word 0x0010d9cd /* 0x0062b999 */
.word 0x00659331 /* 0x001b8352 */
.word 0x000ee40c /* 0x00659331 */
.word 0x004a1ac8 /* 0x000682bb */
.word 0x0043ca37 /* 0x0078abf3 */
.word 0x000875b0 /* 0x0065aa1a */
.word 0x007d136e /* 0x000ee40c */
.word 0x002cd89c /* 0x005e1b0a */
.word 0x00197168 /* 0x007bc241 */
.word 0x000682bb /* 0x0044deec */
.word 0x005e1b0a /* 0x004a1ac8 */
.word 0x002e5ec4 /* 0x002e5ec4 */
.word 0x001b73c3 /* 0x001b73c3 */
.word 0x0051e290 /* 0x00385e99 */
.word 0x00126c59 /* 0x0066a867 */
.word 0x00028371 /* 0x0073835c */
.word 0x0039a1e1 /* 0x0051e290 */
.word 0x001c2ea9 /* 0x006735f9 */
.word 0x004be732 /* 0x007d63e5 */
.word 0x0014fa53 /* 0x00309342 */
.word 0x00385e99 /* 0x00126c59 */
.word 0x006735f9 /* 0x007d0b46 */
.word 0x007d0b46 /* 0x004c7769 */
.word 0x005a6c4a /* 0x00620269 */
.word 0x0076cf29 /* 0x00028371 */
.word 0x00198008 /* 0x005a6c4a */
.word 0x005dc219 /* 0x005ac276 */
.word 0x0026da88 /* 0x001eb9a8 */
.word 0x0066a867 /* 0x0039a1e1 */
.word 0x007d63e5 /* 0x0076cf29 */
.word 0x004c7769 /* 0x0038d3ee */
.word 0x005ac276 /* 0x00276ee5 */
.word 0x0038d3ee /* 0x001c2ea9 */
.word 0x002b35f4 /* 0x00198008 */
.word 0x0074041a /* 0x002b35f4 */
.word 0x00629f68 /* 0x000846cc */
.word 0x0073835c /* 0x004be732 */
.word 0x00309342 /* 0x005dc219 */
.word 0x00620269 /* 0x0074041a */
.word 0x001eb9a8 /* 0x0068fbfc */
.word 0x00276ee5 /* 0x0014fa53 */
.word 0x000846cc /* 0x0026da88 */
.word 0x0068fbfc /* 0x00629f68 */
.word 0x001386ad /* 0x001386ad */
/* Layer 7 (8x1 transposed) */
.word 0x00454828 /* 0x00454828 (untransposed) */
.word 0x003b3864 /* 0x00375fa9 */
.word 0x0015f7fe /* 0x003b3864 */
.word 0x00182f20 /* 0x002e115e */
.word 0x006b686f /* 0x0015f7fe */
.word 0x0002b520 /* 0x000c66bc */
.word 0x001c400a /* 0x00182f20 */
.word 0x003637f8 /* 0x006c41dc */
.word 0x00375fa9 /* 0x006b686f */
.word 0x002e115e /* 0x006bccfc */
.word 0x000c66bc /* 0x0002b520 */
.word 0x006c41dc /* 0x0024c36d */
.word 0x006bccfc /* 0x001c400a */
.word 0x0024c36d /* 0x004fa93f */
.word 0x004fa93f /* 0x003637f8 */
.word 0x007cfb95 /* 0x007cfb95 */
.word 0x001417f8 /* 0x001417f8 */
.word 0x00033821 /* 0x00744760 */
.word 0x00319640 /* 0x00033821 */
.word 0x00002182 /* 0x005b6a95 */
.word 0x004378a7 /* 0x00319640 */
.word 0x0010c942 /* 0x0066a6b9 */
.word 0x00509a79 /* 0x00002182 */
.word 0x007bd511 /* 0x0038d436 */
.word 0x00744760 /* 0x004378a7 */
.word 0x005b6a95 /* 0x007212bd */
.word 0x0066a6b9 /* 0x0010c942 */
.word 0x0038d436 /* 0x007f3301 */
.word 0x007212bd /* 0x00509a79 */
.word 0x007f3301 /* 0x00781bea */
.word 0x00781bea /* 0x007bd511 */
.word 0x00330417 /* 0x00330417 */
/* Layer 6 */
.word 0x002ab0d3
.word 0x006042ad
.word 0x002703d0
.word 0x00445acd
.word 0x0044a7ae
.word 0x0071508b
.word 0x0077c467
.word 0x00737c59
.word 0x00476c75
.word 0x00186ba4
.word 0x0020a9e9
.word 0x004a5bc2
.word 0x003a50a7
.word 0x004a61e3
.word 0x0019152a
.word 0x0019edc3
/* Layer 5 */
.word 0x007b9a3c
.word 0x0042ae00
.word 0x00004bde
.word 0x00650fcc
.word 0x00320368
.word 0x00155b09
.word 0x003ae519
.word 0x0020522a
/* Layer 4 */
.word 0x0056fada
.word 0x005065b8
.word 0x002c04f7
.word 0x0050458c
/* Layer 3 */
.word 0x0078c1dd
.word 0x000d5ed8
/* Layer 2 */
.word 0x0007eafd
/* Layer 1 */
.word 0x00000000

/*
 * Half 2
 */

/* Layer 8 (4x1 transposed) */
.word 0x001df292 /* 0x001df292 (untransposed) */
.word 0x0015d2d1 /* 0x004d6d7e */
.word 0x0010095a /* 0x006bd93a */
.word 0x00362470 /* 0x0006e21c */
.word 0x006785bb /* 0x0015d2d1 */
.word 0x006c9290 /* 0x0032a1c2 */
.word 0x007cc6dd /* 0x006cfee6 */
.word 0x00412fe6 /* 0x00145742 */
.word 0x004d6d7e /* 0x0010095a */
.word 0x0032a1c2 /* 0x0062d4b6 */
.word 0x0062d4b6 /* 0x00635ac2 */
.word 0x0057a770 /* 0x002daf77 */
.word 0x0059efb0 /* 0x00362470 */
.word 0x002785c6 /* 0x0057a770 */
.word 0x0065633a /* 0x006ccb43 */
.word 0x002532bf /* 0x00397ae8 */
.word 0x006bd93a /* 0x006785bb */
.word 0x006cfee6 /* 0x0059efb0 */
.word 0x00635ac2 /* 0x006cd67d */
.word 0x006ccb43 /* 0x0041fee5 */
.word 0x006cd67d /* 0x006c9290 */
.word 0x0056ce68 /* 0x002785c6 */
.word 0x0032ffc5 /* 0x0056ce68 */
.word 0x007b7ef5 /* 0x0054811c */
.word 0x0006e21c /* 0x007cc6dd */
.word 0x00145742 /* 0x0065633a */
.word 0x002daf77 /* 0x0032ffc5 */
.word 0x00397ae8 /* 0x004b6d1a */
.word 0x0041fee5 /* 0x00412fe6 */
.word 0x0054811c /* 0x002532bf */
.word 0x004b6d1a /* 0x007b7ef5 */
.word 0x007aa6e8 /* 0x007aa6e8 */
.word 0x0036de3e /* 0x0036de3e */
.word 0x004ef07b /* 0x000bba6e */
.word 0x0007f904 /* 0x0008032a */
.word 0x007360a7 /* 0x00364683 */
.word 0x0030ba22 /* 0x004ef07b */
.word 0x004a44a4 /* 0x0060df7d */
.word 0x00365bde /* 0x002fa50a */
.word 0x00459e09 /* 0x0009ffdf */
.word 0x000bba6e /* 0x0007f904 */
.word 0x0060df7d /* 0x0000a8fc */
.word 0x0000a8fc /* 0x00189d76 */
.word 0x0071ff1b /* 0x0078507e */
.word 0x001244aa /* 0x007360a7 */
.word 0x0012db10 /* 0x0071ff1b */
.word 0x00255461 /* 0x006381e7 */
.word 0x005c872d /* 0x007221a3 */
.word 0x0008032a /* 0x0030ba22 */
.word 0x002fa50a /* 0x001244aa */
.word 0x00189d76 /* 0x00395d04 */
.word 0x006381e7 /* 0x0035b760 */
.word 0x00395d04 /* 0x004a44a4 */
.word 0x005aba7a /* 0x0012db10 */
.word 0x005da206 /* 0x005aba7a */
.word 0x004be0a7 /* 0x007bcd0c */
.word 0x00364683 /* 0x00365bde */
.word 0x0009ffdf /* 0x00255461 */
.word 0x0078507e /* 0x005da206 */
.word 0x007221a3 /* 0x0033008e */
.word 0x0035b760 /* 0x00459e09 */
.word 0x007bcd0c /* 0x005c872d */
.word 0x0033008e /* 0x004be0a7 */
.word 0x005ff56e /* 0x005ff56e */
/* Layer 7 (8x1 transposed) */
.word 0x0015d39e /* 0x0015d39e (untransposed) */
.word 0x006b4a2d /* 0x00639a9e */
.word 0x0013f609 /* 0x006b4a2d */
.word 0x0012beed /* 0x0005d423 */
.word 0x0025cbf7 /* 0x0013f609 */
.word 0x00385bb5 /* 0x000059c5 */
.word 0x00567162 /* 0x0012beed */
.word 0x000f017b /* 0x000a3d7e */
.word 0x00639a9e /* 0x0025cbf7 */
.word 0x0005d423 /* 0x00064593 */
.word 0x000059c5 /* 0x00385bb5 */
.word 0x000a3d7e /* 0x002d485d */
.word 0x00064593 /* 0x00567162 */
.word 0x002d485d /* 0x005f19c9 */
.word 0x005f19c9 /* 0x000f017b */
.word 0x004bcf0f /* 0x004bcf0f */
.word 0x007df037 /* 0x007df037 */
.word 0x00302d52 /* 0x00376f20 */
.word 0x000f430a /* 0x00302d52 */
.word 0x0062488f /* 0x0030ad80 */
.word 0x00183045 /* 0x000f430a */
.word 0x004ad613 /* 0x003e4f8e */
.word 0x002e67e7 /* 0x0062488f */
.word 0x0017537f /* 0x0013308b */
.word 0x00376f20 /* 0x00183045 */
.word 0x0030ad80 /* 0x005eaa3a */
.word 0x003e4f8e /* 0x004ad613 */
.word 0x0013308b /* 0x001629a3 */
.word 0x005eaa3a /* 0x002e67e7 */
.word 0x001629a3 /* 0x00381e31 */
.word 0x00381e31 /* 0x0017537f */
.word 0x003bf91b /* 0x003bf91b */
/* Layer 6 */
.word 0x00083aa3
.word 0x005c0965
.word 0x000495b3
.word 0x0049dc01
.word 0x002bc1bf
.word 0x0049556b
.word 0x002e7184
.word 0x003aea7b
.word 0x00442152
.word 0x0026b82c
.word 0x0036cfd4
.word 0x00195afd
.word 0x004a013c
.word 0x0050eb34
.word 0x007e69e1
.word 0x0056959a
/* Layer 5 */
.word 0x00202c85
.word 0x0057e699
.word 0x00111560
.word 0x00086270
.word 0x00492879
.word 0x00107a5c
.word 0x00703f91
.word 0x005649a9
/* Layer 4 */
.word 0x001feb81
.word 0x00057b53
.word 0x005bf6d6
.word 0x006401d6
/* Layer 3 */
.word 0x000bdee8
.word 0x007c41bd
/* Layer 2 */
.word 0x0027cefe
/* Layer 1 */
.word 0x007f7b0a
