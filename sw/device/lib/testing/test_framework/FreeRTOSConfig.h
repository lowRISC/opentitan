// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_FREERTOSCONFIG_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_FREERTOSCONFIG_H_

// These macros configure FreeRTOS. A description of each macro can be found
// here: https://www.freertos.org/a00110.html

// NOTE: the macro names below do NOT, and cannot, conform to the style
// guide, since they are specific to FreeRTOS.

// Debugging
#define configGENERATE_RUN_TIME_STATS 0
#define configUSE_APPLICATION_TASK_TAG 0
#define configUSE_TRACE_FACILITY 0

// Hooks
#define configUSE_IDLE_HOOK 0
#define configUSE_MALLOC_FAILED_HOOK 1
#define configUSE_TICK_HOOK 0

// Memory
#define configAPPLICATION_ALLOCATED_HEAP 1
#define configCHECK_FOR_STACK_OVERFLOW 1
#define configMINIMAL_STACK_SIZE 256  // in words
#define configSTACK_DEPTH_TYPE uint16_t
#define configTOTAL_HEAP_SIZE ((size_t)0x8000u)
#define configUSE_MALLOC_FAILED_HOOK 1

// Other
#define configENABLE_BACKWARD_COMPATIBILITY 0
#define configMAX_TASK_NAME_LEN 16
#define configQUEUE_REGISTRY_SIZE 0
#define configUSE_TASK_NOTIFICATIONS 0

// Scheduler
#define configIDLE_SHOULD_YIELD 0
#define configMAX_PRIORITIES 5
#define configTICK_RATE_HZ ((TickType_t)10)  // 100ms tick rate
#define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#define configUSE_PREEMPTION 0
#define configUSE_TIME_SLICING 0
#define configUSE_16_BIT_TICKS 0

// Software timers.
#define configUSE_TIMERS 0

// Synchronization
#define configUSE_COUNTING_SEMAPHORES 0
#define configUSE_MUTEXES 0
#define configUSE_RECURSIVE_MUTEXES 0

// FreeRTOS API functions to include in build image.
#define INCLUDE_vTaskPrioritySet 1
#define INCLUDE_uxTaskPriorityGet 1
#define INCLUDE_vTaskDelete 1
#define INCLUDE_vTaskSuspend 1
#define INCLUDE_eTaskGetState 1
#define INCLUDE_xTaskAbortDelay 1
#define INCLUDE_xTaskGetHandle 1

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_FREERTOSCONFIG_H_
