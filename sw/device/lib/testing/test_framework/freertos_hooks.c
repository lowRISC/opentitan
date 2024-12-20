// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "FreeRTOS.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "task.h"

// NOTE: the function names below do NOT, and cannot, conform to the style
// guide, since they are specific implementations of FreeRTOS defined functions.

/**
 * This is called if configUSE_MALLOC_FAILED_HOOK is set to 1 in
 * FreeRTOSConfig.h, and a call to pvPortMalloc() fails.
 */
void vApplicationMallocFailedHook(void) {
  LOG_INFO("%s",
           "FreeRTOS malloc failed. Increase heap size in FreeRTOSConfig.h");
  irq_global_ctrl(false);
  abort();
}

/**
 * This is called if configCHECK_FOR_STACK_OVERFLOW is set to 1 or 2 in
 * FreeRTOSConfig.h, and a task detects a stack overflow.
 */
void vApplicationStackOverflowHook(TaskHandle_t xTask, char *pcTaskName) {
  LOG_INFO("FreeRTOS stack overflow. Increase stack size of task: %s",
           pcTaskName);
  irq_global_ctrl(false);
  abort();
}
