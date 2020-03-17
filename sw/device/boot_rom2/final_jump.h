// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0`

#ifndef OPENTITAN_SW_DEVICE_BOOT_ROM2_FINAL_JUMP_H_
#define OPENTITAN_SW_DEVICE_BOOT_ROM2_FINAL_JUMP_H_

#include <stdint.h>
#include <stdnoreturn.h>

/**
 * Represents arguments to be passed onto the next stage of boot.
 */
typedef struct next_stage_args {
  /**
   * The absolute address of the top of the stack for the next stage.
   * The next stage is responsible for using this value to set up its stack.
   *
   * Note that |final_jump()| may modify this value to allocate some stack space
   * to pass arguments to the next stage.
   */
  void *stack_start;
} next_stage_args_t;

/**
 * Represents the entry point into the next stage of boot. This should point to
 * the absolute address of the first instruction to be executed after the mask
 * ROM portion of memory is locked down.
 */
typedef void (*entrypoint_t)(next_stage_args_t *);

/**
 * Performs the "final jump": i.e., does a deep clean of machine state, locks
 * down the mask ROM memory, and jumps to |entry|.
 *
 * All pointers in |args| must be into RAM, and should be into non-stack memory.
 *
 * @param entry the entry point for the next boot stage.
 * @param args args to pass to the next boot stage.
 */
noreturn void final_jump(entrypoint_t entry, next_stage_args_t args);

#endif  // OPENTITAN_SW_DEVICE_BOOT_ROM2_FINAL_JUMP_H_
