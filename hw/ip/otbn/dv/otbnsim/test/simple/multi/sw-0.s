/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Triggering multiple errors from a single SW instruction (underflow
  call stack for value to store and also give a bad address).
*/
  sw x1, -1(x0)
