// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_ASM_H_
#define OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_ASM_H_

/**
 * Multi-bit boolean values for use in assembly code.
 *
 * Please use `multibits.h` instead when writing C code.
 */
<%
from mubi import prim_mubi
%>\
% for n in range(1, n_max_nibbles + 1):
<%
  nbits = n * 4
%>\

/**
 * ${nbits}-bits boolean values
 */
#define MULTIBIT_ASM_BOOL${nbits}_TRUE 0x${prim_mubi.mubi_value_as_hexstr(True, nbits)}
#define MULTIBIT_ASM_BOOL${nbits}_FALSE 0x${prim_mubi.mubi_value_as_hexstr(False, nbits)}
% endfor

#endif  // OPENTITAN_SW_DEVICE_LIB_BASE_MULTIBITS_ASM_H_
