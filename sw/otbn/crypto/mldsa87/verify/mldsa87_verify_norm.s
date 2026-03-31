/* Copyright lowRISC contributors (OpenTitan project). */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Unmasked infinity norm bound check. */

.globl check_infinity_norm

.text

/**
 * Check the infinity norm of a polynomial against a bound b.
 *
 * The infinity norm of a polynomial |X|_inf is defined as max_i
 * |X[i] mod^+- q|. This routine sets w0 = 2^256-1 if |X|_inf < b, else w0 = 0.
 *
 * The bound b is assumed to be provided in a 8-element vectorized form.
 *
 * @param[in] x2: DMEM address of the input polynomial X.
 * @param[in] x3: DMEM address of the bound vector b.
 * @param[out]: w0: 2^256-1 if |x|_inf < b, else w0 = 0.
 */
check_infinity_norm:
  /* Push clobbered registers onto the stack. */
  .irp reg, x2, x4
    sw \reg, 0(x31)
    addi x31, x31, 4
  .endr

  /*
    For the sake of simplicity, let us start with a weaker notion of the bound
    check. A coefficient x of a polynomial is within bounds in the unreduced
    representation if |x mod^+- Q| <= b. In other words, if either x <= b or
    x => (Q - b) is the case as shown below where the 'v' marks the valid
    intervals and 'i' the invalid one.

                | vvvvvvv | iiiiiiiiiiiiiiiii | vvvvvvv |
                ^         ^                   ^         ^
                0         b                 Q - b       Q

    To simplify this check, we first compute x + b mod Q which will shift the
    valid intervals into a continuous range such that

                | vvvvvvv | vvvvvvv | iiiiiiiiiiiiiiiii |
                ^         ^         ^                   ^
                0         b       2 * b                 Q

    Now all that is left is to verify x <= 2 * b, which we can do by adding the
    value x + b mod Q to 2^31 - 1 - (2 * b) and check whether the MSB is set
    or not. It is not set if and only if |x mod^+- Q| <= b. All the infinity
    norm checks in ML-DSA are strict inequalities, hence we need to execute the
    above algorithm on the bounds b - 1.
  */

  /* Load the bound constant and subtract 1 from it. */
  addi x4, x0, 2
  bn.lid x4, 0(x3)

  bn.not w0, w31
  bn.shv.8s w0, w0 >> 31
  bn.subv.8s w2, w2, w0

  /* b' = 2 * (b - 1). */
  bn.addv.8S w3, w2, w2

  /* 2^31 - 1 - b'. */
  bn.not w4, w31
  bn.shv.8s w4, w4 >> 1
  bn.subv.8S w4, w4, w3

  /* Flag, 0 if and only if |X[i]|_inf < b for 0 <= i < 256. */
  bn.xor w1, w1, w1

  /* Iterate over the entire polynomial in chunks of 8 coefficients and check
     their infinity norm in parallel. */
  loopi 32, 5
    bn.lid x0, 0(x2++)

    /* x = X[i] + (b - 1) mod Q. */
    bn.addvm.8S w0, w0, w2
    /* (2^31 - 1 - (2 * (b - 1)) + x. */
    bn.addv.8S w0, w0, w4
    /* Isolate the MSB. */
    bn.shv.8S w0, w0 >> 31

    /* If the MSB is 0, then the 8 coefficients have passed the bound check. */
    bn.or w1, w1, w0
    /* End of loop */

  /* Set w0 = 2^256-1 if |X[i] mod^+- Q| < b for all 0 <= i < 256. */
  bn.subi w0, w31, 1
  bn.cmp w1, w31, FG0
  bn.sel w0, w0, w31, FG0.Z

  /* Restore clobbered general-purpose registers. */
  .irp reg, x4, x2
    addi x31, x31, -4
    lw \reg, 0(x31)
  .endr

  ret
