// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/freertos_hooks.h"

#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/vendor/freertos_freertos_kernel/include/FreeRTOS.h"

// NOTE: the function names below do NOT, and cannot, conform to the style
// guide, since they are specific implementations of FreeRTOS defined functions.

void vApplicationMallocFailedHook(void) {
  // TODO: communicate this event back to the host.
  LOG_INFO("Malloc Failed.");
  taskDISABLE_INTERRUPTS();
  abort();
}

void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName) {
  // TODO: communicate this event back to the host.
  LOG_INFO("Stack Overflow.");
  (void)pcTaskName;
  (void)pxTask;
  taskDISABLE_INTERRUPTS();
  abort();
}
