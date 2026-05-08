/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Secure masked gadgets. */

.globl sec_a2b_8x32
.globl sec_b2a_8x32
.globl sec_add_8x32
.globl sec_unmask_8x32
.globl sec_unmask
.globl sec_bound_check
.globl sec_decompose

/*

The masking accelerator supports three functions that operate in a vectroized
fashion on 8 coefficients in a single WDR. The interface consists of four input
WSRs to pass two shared vectors to the accelerator, MAI_IN0_S0 and MAI_IN0_S1
for the first input and MAI_IN1_S0 and MAI_IN1_S1 for the second input which is
only used for the second summand in the secure addition. The shared result of
the operation can be read in the MAI_RES_S0 and MAI_RES_S1 WSRs. The interface
has a single control register MAI_CTRL that instruments the accelerator and
immediately triggers a computation upon seeing a valid configuration value.

Note that some routines of this modules draw randomness from URND for masking
purposes, hence while an MAI operation is ongoing, URND bits shall not be
shared between different routines.

Most routines of this module are a direct implementation of the gadgets in the
work of Azouaoui et al. [1].

[1] https://tches.iacr.org/index.php/TCHES/article/view/11158/10597

*/

/*
 * Configuration values for the MAI_CTRL register.
 */
.set MAI_CTRL_A2B, 0x1
.set MAI_CTRL_B2A, 0x3
.set MAI_CTRL_ADD, 0x5

.text

/* MAI interface polling routine. */
_mai_poll:
  csrrs x20, MAI_STATUS, x0
  andi x20, x20, 0x1
  bne x20, x0, _mai_poll
  ret

/**
 * Convert the arithmetic sharing of a vector of 8 coefficients (x0_A, x1_A) to
 * a Boolean sharing (x0_B, x1_B).
 *
 * @param[in]  w0: x0_A, first arithmetic share.
 * @param[in]  w1: x1_A, second arithmetic share.
 * @param[out] w0: x0_B, first Boolean share.
 * @param[out] w1: x1_B, second Boolean share
 */
sec_a2b_8x32:
  /* Write the two shares to the input WSRs (intersperse with configuration of
     MAI_CTRL to not access both shares in subsequent instructions). */
  bn.wsrw MAI_IN0_S0, w0
  addi x20, x0, MAI_CTRL_A2B
  bn.wsrw MAI_IN0_S1, w1

  /* Trigger the conversion. */
  csrrw x0, MAI_CTRL, x20

  /* TODO: Replace with deterministic wait, once exact latency is known. */
  jal x1, _mai_poll

  /* Read back the result. */
  bn.wsrr w0, MAI_RES_S0
  bn.xor w31, w31, w31 /* dummy */
  bn.wsrr w1, MAI_RES_S1

  ret

/**
 * Convert the Boolean sharing of a vector of 8 coefficients (x0_B, x1_B) to a
 * arithmetic sharing (x0_A, x1_A).
 *
 * @param[in]  w0: x0_B, first Boolean share.
 * @param[in]  w1: x1_B, second Boolean share.
 * @param[out] w0: x0_A, first arithmetic share.
 * @param[out] w1: x1_A, second arithmetic share
 */
sec_b2a_8x32:
  /* Write the two shares to the input WSRs (intersperse with configuration of
     MAI_CTRL to not access both shares in subsequent instructions). */
  bn.wsrw MAI_IN0_S0, w0
  addi x20, x0, MAI_CTRL_B2A
  bn.wsrw MAI_IN0_S1, w1

  /* Trigger the conversion. */
  csrrw x0, MAI_CTRL, x20

  /* TODO: Replace with deterministic wait, once latency is known. */
  jal x1, _mai_poll

  /* Read back the result. */
  bn.wsrr w0, MAI_RES_S0
  bn.xor w31, w31, w31 /* dummy */
  bn.wsrr w1, MAI_RES_S1

  ret

/**
 * Calculate a vectorized addition modulo 2^32 of 8 Boolean-shared coefficients.
 *
 * @param[in]  w0: x0_B, first Boolean share of x
 * @param[in]  w1: x1_B, second Boolean share of x.
 * @param[in]  w2: y0_B, first Boolean share of y
 * @param[in]  w3: y1_B, second Boolean share of y.
 * @param[out] w0: z0_B, first Boolean share of the result z = x + y.
 * @param[out] w1: z1_B, second Boolean share of the result z = x + y.
 */
sec_add_8x32:
  /* Write the two summands to the input WSRs (intersperse with configuration of
     MAI_CTRL to not access both shares in subsequent instructions). */
  bn.wsrw MAI_IN0_S0, w0
  bn.wsrw MAI_IN1_S0, w2

  addi x20, x0, MAI_CTRL_ADD

  bn.wsrw MAI_IN0_S1, w1
  bn.wsrw MAI_IN1_S1, w3

  /* Trigger the conversion. */
  csrrw x0, MAI_CTRL, x20

  /* TODO: Replace with deterministic wait, once latency is known. */
  jal x1, _mai_poll

  /* Read back the result. */
  bn.wsrr w0, MAI_RES_S0
  bn.xor w31, w31, w31 /* dummy */
  bn.wsrr w1, MAI_RES_S1

  ret

/**
 * Securely unmask a vector of 8 Boolean-shared coefficients.
 *
 * This is an implementation of the `SecUnMask` function (Algorithm 3 in [1]).
 *
 * @param[in]  w0: x0_B, first Boolean share of x
 * @param[in]  w1: x1_B, second Boolean share of x.
 * @param[out] w0: x, unmasked value x.
 */
sec_unmask_8x32:
  /* Sample a fresh random mask and XOR it to the shares before unmasking. */
  bn.wsrr w20, URND

  bn.xor w0, w0, w20
  bn.xor w31, w31, w31 /* dummy */
  bn.xor w1, w1, w20

  bn.xor w0, w0, w1

  ret

/**
 * Compute a secure less-than equal operation on 8 Boolean-shared coefficients.
 *
 * This gadgets returns 2^32-1 for a coefficient x in [0, 2^32-1] if x <= b for
 * a bound b < 2^32-1. This is an implementation fo the `SecLeq` function
 * (Algorithm 4 in [1]).
 *
 * Note that the WDRs w0-w3 are clobbered.
 *
 * @param[in]  w0: x0_B, first Boolean share of x.
 * @param[in]  w1: x1_B, second Boolean share of x.
 * @param[in]  w2: b, vectorized bound b.
 * @param[out] w0: the result of the bound check.
 */
sec_leq_8x32:
  /* Calculate the bound b = 2^32 - b - 1. */
  bn.not w3, w31
  bn.subv.8S w2, w3, w2

  bn.xor w3, w3, w3

  /* Compute y = x + b mod 2^32. */
  jal x1, sec_add_8x32
  jal x1, sec_unmask_8x32

  /* x = 2^32 - 1 if x <= b, else 0. */
  bn.shv.8S w0, w0 >> 31
  bn.subv.8S w0, w31, w0

  ret

/**
 * Calculate a secure bound check on the arithmetically shared coefficients of
 * a polynomial.
 *
 * This is a masked variant of the infinity norm check that verifies for a
 * polynomial X that its infinity norm is smaller than a given bound b, i.e.,
 * |X|_inf < b. For a detailed explanation of the inner workings of this
 * algorithm see `mldsa87_verify_norm.s`.
 *
 * This routine implements the `SecBoundCheck` function (Algorithm 5 in [1]).
 *
 * @param[in]  x2: DMEM address of the first arith. share of the polynomial X.
 * @param[in]  x3: DMEM address of the second arith. share of the polynomial X.
 * @param[in]  x4: DMEM address of the vectorized bound b (32 bytes).
 * @param[out] w0: result, 2^32-1 if the |X|_inf < b, else 0.
 */
sec_bound_check:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load the bound constant b and subtract 1 from it. */
  bn.lid x0, 0(x4)
  bn.not w1, w31
  bn.shv.8s w1, w1 >> 31
  bn.subv.8s w4, w0, w1

  /* b' = 2 * (b - 1). */
  bn.addv.8S w5, w4, w4

  /* First and second share WDR pointers. */
  addi x5, x0, 0
  addi x6, x0, 1

  bn.not w6, w31 /* flag */

  /* Iterate over the entire polynomial in chunks of 8 coefficients and check
     their infinity norm in parallel. */
  loopi 32, 7
    /* Load the first share x0 and add the bound b, x0 + b mod Q. */
    bn.lid x5, 0(x2++)
    bn.addvm.8S w0, w0, w4

    /* Slot b' into w2 for `seq_leq`. */
    bn.mov w2, w5

    bn.lid x6, 0(x3++)

    /* Convert to Boolean shares and invoke `sec_leq` with b'. */
    jal x1, sec_a2b_8x32
    jal x1, sec_leq_8x32

    bn.and w6, w6, w0
    /* End of loop */

  /* w0 = 2^256 - 1 if |X|_inf < b, else 0. */
  bn.not w0, w31
  bn.cmp w6, w0, FG0
  bn.sel w0, w0, w31, FG0.Z

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Securely decompose an arithmetically shared polynomial X = X0_A + X1_A into
 * two polynomials W0 = W00_A + W01_A and W1 composed of the lower and higher
 * bits of each coefficient in X respectively. W0 will be arithmetically shared
 * while W1 is unmasked.
 *
 * This routine is a masked variant of the polynomial decomposition. See
 * `mldsa87_verify_rounding.s` for detailed breakdown of the individual
 * computational steps. This is an implementation of the `SecDecompose`
 * function (Algorithm 7 in [1]).
 *
 * Note that this routine will overwrite the inputs X0_A and X1_A with W00_A
 * and W01_A.
 *
 * @param[in] x2: DMEM address of the first input share polynomial X0_A and
 *                the output polynomial W00_A.
 * @param[in] x3: DMEM address of the second input share polynomial X1_A and
 *                the output polynomial W01_A.
 * @param[in] x4: DMEM address of output polynomial W1.
 */
sec_decompose:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* Load decomposition constants into w4-w7. */
  addi x5, x0, 4
  la x6, _sec_decompose_gamma2
  bn.lid x5++, 0(x6)  /* w4 = GAMMA2 */
  bn.lid x5++, 32(x6) /* w5 = (ALPHA, ALPHA^-1) */

  bn.not w6, w31
  bn.shv.8s w6, w6 >> 28 /* w6 = (0x0000000f, 0x0000000f, ..., 0x0000000f) */
  bn.shv.8s w7, w6 >> 3  /* w7 = (0x00000001, 0x00000001, ..., 0x00000001) */

  /* WDR pointers. */
  addi x5, x0, 8  /* x0 */
  addi x6, x0, 9  /* x1 */

  loopi 32, 16
    bn.lid x5, 0(x2)

    /*
     * Part 1: b = ALPHA^-1 * (x0 + GAMMA2) - 1, with b = b0 + b1 mod Q.
     */

    /* b0 = x0 + GAMMA2 mod Q. */
    bn.addvm.8S w0, w8, w4

    /* b0 = ALPHA^-1 * b - 1 mod Q. */
    bn.mulvml.8S w0, w0, w5, 1
    bn.addvm.8S w0, w0, w31 /* cond sub */
    bn.subvm.8S w0, w0, w7

    bn.xor w31, w31, w31 /* dummy */

    /* b1 = ALPHA^-1 * x1 mod Q. */
    bn.lid x6, 0(x3++)
    bn.mulvml.8S w1, w9, w5, 1
    bn.addvm.8S w1, w1, w31 /* cond sub */

    /* Convert (b0, b1) to Boolean shares. */
    jal x1, sec_a2b_8x32
    jal x1, sec_unmask_8x32

    /*
     * Part 2: w1 = (b0 ^ b1) mod 16, w0 = b0 - ALPHA * w1.
     */

    /* w1 = b mod 16. */
    bn.and w0, w0, w6

    /* w0 = b0 - ALPHA * w1. */
    bn.mulvl.8S w1, w0, w5, 0
    bn.subvm.8S w8, w8, w1

    bn.sid x5, 0(x2++)
    bn.sid x0, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

/**
 * Securely unmask an arithmetically shared polynomial.
 *
 * This routine is a polynomial wrapper around `sec_unmask_8x32` which in turn
 * implements the `SecUnMask` function (Algorithm 3 in [1]).
 *
 * @param[in]  x2: DMEM address of the first arithmetic polynomial share.
 * @param[in]  x3: DMEM address of the second arithmetic polynomial share.
 * @param[out] x4: DMEM address of the resulting unmasked polynomial.
 */
sec_unmask:
 /* Push clobbered registers onto the stack. */
  .irp reg, x2, x3, x4, x5, x6
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /* WDR pointers. */
  addi x5, x0, 0
  addi x6, x0, 1

  /* Iterate over the shared polynomial in steps of eight coefficients. */
  loopi 32, 6
    /* Load 8 arithmetically shared coefficients into w0 and w1. */
    bn.lid x5, 0(x2++)
    bn.xor w31, w31, w31 /* dummy */
    bn.lid x6, 0(x3++)

    /* Convert the coefficients to Boolean shares before unmasking them. */
    jal x1, sec_a2b_8x32
    jal x1, sec_unmask_8x32

    /* Store unmasked coefficients into the output location. */
    bn.sid x5, 0(x4++)
    /* End of loop */

  /* Restore clobbered general-purpose registers. */
  .irp reg, x6, x5, x4, x3, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret

.data
.balign 32

/* GAMMA2 = (Q - 1) / 32. */
_sec_decompose_gamma2:
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00
.word 0x0003ff00

_sec_decompose_alphas:
.word 0x0007fe00 /* ALPHA = 2 * GAMMA1 = (Q - 1) / 16 */
.word 0x007f0009 /* ALPHA^-1 * 2^32 mod Q (Montgomery domain) */
.zero 24 /* Padding */
