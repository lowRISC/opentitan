// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/coverage/api_asm.h"

// PRAGMA_COVERAGE: section(__llvm_prf_cnts_head)
// PRAGMA_COVERAGE: autogen start

  .section .text, "ax"

  .global covfunc_nested_hit
  .type covfunc_nested_hit, @function
covfunc_nested_hit:
  COVERAGE_ASM_AUTOGEN_MARK(t6,0)
  ret
  .size covfunc_nested_hit, .-covfunc_nested_hit

  .global covfunc_hit
  .type covfunc_hit, @function
covfunc_hit:
  COVERAGE_ASM_AUTOGEN_MARK(t6,1)
  j covfunc_nested_hit
  .size covfunc_hit, .-covfunc_hit

  .global covfunc_nested_miss
  .type covfunc_nested_miss, @function
covfunc_nested_miss:
  COVERAGE_ASM_AUTOGEN_MARK(t6,2)
  ret
  .size covfunc_nested_miss, .-covfunc_nested_miss

  .global covfunc_miss
  .type covfunc_miss, @function
covfunc_miss:
  COVERAGE_ASM_AUTOGEN_MARK(t6,3)
  j covfunc_nested_miss
  .size covfunc_miss, .-covfunc_miss
