/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */
/*
  Bad target address and jump at end of loop
*/
  loopi 1, 1
    jal x1, .+2
