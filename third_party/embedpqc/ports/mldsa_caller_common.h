// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_MLDSA_CALLER_COMMON_H_
#define OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_MLDSA_CALLER_COMMON_H_

#define MLDSA_CALLER_WITH_STACK(target_name, stack_reg)               \
  .global target_name##_with_stack;                                   \
  .type target_name##_with_stack, @function;                          \
  .section /**/.text.target_name##_with_stack, "ax", @progbits;       \
  target_name##_with_stack:;                                          \
  /* Allocate 16B to maintain 16-byte stack alignment (RV32 ABI). */; \
  /* We save sp (4B) and ra (4B), leaving 8B of padding. */;          \
  addi stack_reg, stack_reg, -16;                                     \
  sw sp, 0(stack_reg);                                                \
  sw ra, 4(stack_reg);                                                \
  mv sp, stack_reg;                                                   \
  call target_name;                                                   \
  lw ra, 4(sp);                                                       \
  lw sp, 0(sp);                                                       \
  ret;                                                                \
  .size target_name##_with_stack, .- target_name##_with_stack

#endif  // OPENTITAN_THIRD_PARTY_EMBEDPQC_PORTS_MLDSA_CALLER_COMMON_H_
