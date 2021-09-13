/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Triggering multiple errors from a single LW instruction (overflow
  call stack and also give a bad address).

  We expect just to see the bad address error, since there is no
  result from the load so nothing to write to the call stack anyway.
*/
  loopi   8, 1
    addi  x1, x0, 0

  lw    x1, -1(x0)
