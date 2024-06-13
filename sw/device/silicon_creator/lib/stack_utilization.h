// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_STACK_UTILIZATION_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_STACK_UTILIZATION_H_
#include <stdint.h>

#include "sw/device/silicon_creator/lib/stack_utilization_asm.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Examine stack utilization.
 */
#ifdef STACK_UTILIZATION_CHECK
void stack_utilization_print(void);
#else
#define stack_utilization_print() \
  do {                            \
  } while (0)
#endif

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_STACK_UTILIZATION_H_
