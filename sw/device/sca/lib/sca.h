// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_
#define OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_

#include "sw/device/lib/dif/dif_uart.h"

#include <stdint.h>

/**
 * @file
 * @brief Side-channel analysis support library.
 */

/**
 * Initializes the peripherals (pinmux, uart, gpio, and timer) used by SCA code.
 */
void sca_init(void);

/**
 * Returns a handle to the intialized UART device.
 *
 * @param[out] uart_out Handle to the initialized UART device.
 */
void sca_get_uart(const dif_uart_t **uart_out);

/**
 * Sets capture trigger high.
 *
 * The actual trigger signal used for capture is a combination (logical AND) of:
 * - GPIO15 enabled here, and
 * - the busy signal of the AES unit. This signal will go high 40 cycles
 *   after aes_manual_trigger() is executed below and remain high until
 *   the operation has finished.
 */
void sca_set_trigger_high(void);

/**
 * Sets capture trigger low.
 */
void sca_set_trigger_low(void);

/**
 * Functions called by `sca_call_and_sleep()` must conform to this prototype.
 */
typedef void (*sca_callee)(void);

/**
 * Calls the given function and puts Ibex to sleep.
 *
 * This function can be used to minimize noise while capturing power traces for
 * side-channel attacks, in which case `callee` would trigger the operation of
 * interest, typically a crypto operation, on the target device.
 *
 * @param callee Function to call before putting Ibex to sleep.
 * @param sleep_cycles Number of cycles to sleep.
 */
void sca_call_and_sleep(sca_callee callee, uint32_t sleep_cycles);

/**
 * Prints an error message over UART if the given condition evaluates to false.
 * TODO: Remove once there is a CHECK version that does not require test
 * library dependencies.
 */
#define CHECK(condition, ...)                             \
  do {                                                    \
    if (!(condition)) {                                   \
      /* NOTE: because the condition in this if           \
         statement can be statically determined,          \
         only one of the below string constants           \
         will be included in the final binary.*/          \
      if (GET_NUM_VARIABLE_ARGS(_, ##__VA_ARGS__) == 0) { \
        LOG_ERROR("CHECK-fail: " #condition);             \
      } else {                                            \
        LOG_ERROR("CHECK-fail: " __VA_ARGS__);            \
      }                                                   \
    }                                                     \
  } while (false)

#endif  // OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_
