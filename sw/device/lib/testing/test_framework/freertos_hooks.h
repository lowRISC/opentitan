// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_FREERTOS_HOOKS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_FREERTOS_HOOKS_H_

#include "sw/vendor/freertos_freertos_kernel/include/FreeRTOS.h"
#include "sw/vendor/freertos_freertos_kernel/include/task.h"

// NOTE: the function names below do NOT, and cannot, conform to the style
// guide, since they are specific implementations of FreeRTOS defined functions.

/**
 * This is called if configUSE_MALLOC_FAILED_HOOK is set to 1 in
 * FreeRTOSConfig.h, and a call to pvPortMalloc() fails.
 */
void vApplicationMallocFailedHook(void);

/**
 * This is called if a stack overflow is detected, and
 * configCHECK_FOR_STACK_OVERFLOW is set to 1 or 2 in FreeRTOSConfig.h.
 *
 * @param pxTask FreeRTOS task handle.
 * @param pcTaskName
 */
void vApplicationStackOverflowHook(TaskHandle_t pxTask, char *pcTaskName);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_FREERTOS_HOOKS_H_
