/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Secure masked gadgets. */

.globl sec_a2b_8x32
.globl sec_b2a_8x32

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
 * @param[in]  w0: x0_B, first arithmetic share.
 * @param[in]  w1: x1_B, second arithmetic share.
 * @param[out] w0: x0_A, first Boolean share.
 * @param[out] w1: x1_A, second Boolean share
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
