// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/boot_rom2/final_jump.h"

#include "sw/device/lib/base/memory.h"

static const uintptr_t kStackAlign = alignof(uint32_t);

/**
 * The "actual" final jump, which is implemented in assembly. The C portion is
 * merely the part that can be safely executed before the stack is bleached.
 */
noreturn void _final_jump_asm(entrypoint_t entry, void *next_stack_start);

noreturn void final_jump(entrypoint_t entry, next_stage_args_t args) {
  // Reserve space at the bottom of the stack for the next stage args.
  //
  // This code copies the value of |args| to the bottom of the next stage's
  // stack, where we can be sure it will not be clobbered by the current stack
  // being clobbered. We also move the bottom of the next stage's stack up to
  // account for the newly allocated space, and update the
  // next-stage-stack-pointer in the next stage args to account for that.
  uint8_t *next_stack_start =
      ((uint8_t *)args.stack_start) - sizeof(next_stage_args_t);
  // Ensure that the stack is still word-aligned.
  next_stack_start -= ((uintptr_t)next_stack_start) % kStackAlign;

  args.stack_start = next_stack_start;
  memcpy(next_stack_start, &args, sizeof(next_stage_args_t));

  _final_jump_asm(entry, next_stack_start);
}
