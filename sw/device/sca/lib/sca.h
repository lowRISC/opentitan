// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_
#define OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_uart.h"

/**
 * @file
 * @brief Side-channel analysis support library.
 */

/**
 * Trigger sources.
 *
 * The trigger signal for a peripheral is based on its clkmgr_aon_idle signal.
 * These values must match the values in chiplevel.sv.tpl.
 */
typedef enum sca_trigger_source {
  /**
   * Use AES for capture trigger.
   *
   * The trigger signal will go high 40 cycles after `dif_aes_trigger()` is
   * called and remain high until the operation is complete.
   */
  kScaTriggerSourceAes,
  /**
   * Use HMAC for capture trigger.
   */
  kScaTriggerSourceHmac,
  /**
   * Use KMAC for capture trigger.
   */
  kScaTriggerSourceKmac,
  /**
   * Use OTBN (IO_DIV4 clock) for capture trigger.
   */
  kScaTriggerSourceOtbnIoDiv4,
  /**
   * Use OTBN for capture trigger.
   */
  kScaTriggerSourceOtbn,
} sca_trigger_source_t;

/**
 * Peripherals.
 *
 * Constants below are bitmasks that can be used to specify a set of
 * peripherals.
 *
 * See also: `sca_peripherals_t`.
 */
typedef enum sca_peripheral {
  /**
   * EDN.
   */
  kScaPeripheralEdn = 1 << 0,
  /**
   * CSRNG.
   */
  kScaPeripheralCsrng = 1 << 1,
  /**
   * Entropy source.
   */
  kScaPeripheralEntropy = 1 << 2,
  /**
   * AES.
   */
  kScaPeripheralAes = 1 << 3,
  /**
   * HMAC.
   */
  kScaPeripheralHmac = 1 << 4,
  /**
   * KMAC.
   */
  kScaPeripheralKmac = 1 << 5,
  /**
   * OTBN.
   */
  kScaPeripheralOtbn = 1 << 6,
  /**
   * USB.
   */
  kScaPeripheralUsb = 1 << 7,
} sca_peripheral_t;

/**
 * A set of peripherals.
 *
 * This type is used for specifying which peripherals should be enabled when
 * calling `sca_init()`. Remaining peripherals will be disabled to reduce noise
 * during SCA.
 *
 * See also: `sca_peripheral_t`, `sca_init()`.
 */
typedef uint32_t sca_peripherals_t;

/**
 * Initializes the peripherals (pinmux, uart, gpio, and timer) used by SCA code.
 *
 * @param trigger Peripheral to use for the trigger signal.
 * @param enable Set of peripherals to enable. Remaining peripherals will
 * be disabled to reduce noise during SCA.
 */
void sca_init(sca_trigger_source_t trigger, sca_peripherals_t enable);

/**
 * Returns a handle to the intialized UART device.
 *
 * @return Handle to the initialized UART device.
 */
const dif_uart_t *sca_get_uart(void);

/**
 * Sets capture trigger high.
 *
 * The actual trigger signal used for capture is a combination (logical AND) of:
 * - the trigger gate enabled here, and
 * - the busy signal of the peripheral of interest.
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
 * Prints an error message over UART if the given DIF evaluates to anthing but
 * kDifOk.
 * TODO: Remove once there is a CHECK_DIF_OK version that does not require test
 * library dependencies.
 */
#define CHECK_DIF_OK(dif_call, ...)                  \
  do {                                               \
    if (dif_call != kDifOk) {                        \
      /* NOTE: because the condition in this if      \
         statement can be statically determined,     \
         only one of the below string constants      \
         will be included in the final binary.*/     \
      if (OT_VA_ARGS_COUNT(_, ##__VA_ARGS__) == 0) { \
        LOG_ERROR("DIF-fail: " #dif_call);           \
      } else {                                       \
        LOG_ERROR("DIF-fail: " __VA_ARGS__);         \
      }                                              \
    }                                                \
  } while (false)
#endif  // OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_
