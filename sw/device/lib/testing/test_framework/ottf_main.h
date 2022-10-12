// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MAIN_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MAIN_H_

#include <stdbool.h>

#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/test_framework/FreeRTOSConfig.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

/**
 * @file
 * @brief Entrypoint definitions for on-device tests
 */

/**
 * Entry point for a SW on-device (or chip-level) test.
 *
 * This function should be defined externally in a standalone SW test, linked
 * together with this library. This library provides a `main()` function that
 * does test harness setup, initializes FreeRTOS, and starts a FreeRTOS task
 * that executes `test_main()`.
 *
 * @return success or failure of the test as boolean.
 */
extern bool test_main(void);

/**
 * OTTF Constants.
 */
enum {
  kOttfFreeRtosMinStackSize = configMINIMAL_STACK_SIZE,
};

/**
 * Returns the UART that is the console device.
 */
dif_uart_t *ottf_console(void);

/**
 * TODO: add description
 */
extern bool manufacturer_pre_test_hook(void);

/**
 * TODO: add description
 */
extern bool manufacturer_post_test_hook(void);

/**
 * Forward declaration of the function pointer prototype to which FreeRTOS (and
 * transitively OTTF) task functions must conform.  We use a forward declaration
 * here to hide FreeRTOS internals from OTTF users.
 *
 * This declaration should match the `TaskFunction_t` type declaration in
 * `<freertos kernel>/include/projdefs.h`.
 */
typedef void (*ottf_task_t)(void *);

/**
 * Create a FreeRTOS task.
 *
 * Tasks should be implemented as functions that never return. However, they may
 * delete themselves using the `ottf_task_delete_self()` function defined below.
 *
 * Additionally, tasks are always run at a priority level higher than that of
 * the FreeRTOS idle task's (which is a priority of 0).
 *
 * See the FreeRTOS `xTaskCreate` documentation for more details:
 * https://www.freertos.org/a00125.html.
 *
 * @param task_function The name of the function that implements the task.
 * @param task_name A task identification string used to help debugging.
 * @param task_stack_depth The amount of memory to reserve for the task's stack.
 * @param task_priority The numerical priority of the task.
 * @return A boolean encoding the success of the operation.
 */
bool ottf_task_create(ottf_task_t task_function, const char *task_name,
                      configSTACK_DEPTH_TYPE task_stack_depth,
                      uint32_t task_priority);
/**
 * Yield control flow to another FreeRTOS task of equal or higher priority.
 *
 * Note, if there are no other tasks of equal or higher priority, then the
 * calling task will continue executing. See the FreeRTOS `taskYIELD`
 * documentation for more details:
 * https://www.freertos.org/a00020.html#taskYIELD.
 */
void ottf_task_yield(void);

/**
 * Delete the calling FreeRTOS task.
 *
 * See the FreeRTOS `vTaskDelete` documentation for more details:
 * https://www.freertos.org/a00126.html.
 */
void ottf_task_delete_self(void);

/**
 * Returns the name of the currently executing FreeRTOS task.
 *
 * See the FreeRTOS `pcTaskGetName` documentation for more details:
 * https://www.freertos.org/a00021.html#pcTaskGetName.
 */
char *ottf_task_get_self_name(void);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MAIN_H_
