/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/**
 * Fake primality-test routine.
 *
 * This will cause an error if called; it should be used for tests where
 * calling a full primality test indicates failure (such as a test in which the
 * candidate prime should fail earlier checks before being evaluated for
 * primality).
 */
.globl miller_rabin
miller_rabin:
  unimp
