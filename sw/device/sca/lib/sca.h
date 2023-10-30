// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_
#define OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_

#include <stdint.h>

#include "sw/ip/uart/dif/dif_uart.h"

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
   * The trigger signal will go high 320 cycles after `dif_aes_trigger()` is
   * called and remain high until the operation is complete.
   */
  kScaTriggerSourceAes = 0,
  /**
   * Use HMAC for capture trigger.
   */
  kScaTriggerSourceHmac = 1,
  /**
   * Use KMAC for capture trigger.
   */
  kScaTriggerSourceKmac = 2,
  /**
   * Use OTBN for capture trigger.
   */
  kScaTriggerSourceOtbn = 3,
} sca_trigger_source_t;

/**
 * Trigger type.
 */
typedef enum sca_trigger_type {
  /**
   * Use the precise hardware capture trigger gateable by software. If selected,
   * the actual capture trigger is generated based on the clkmgr_aon_idle signal
   * of the peripheral corresponding to selected trigger source.
   *
   * Note that this is available on FPGA only.
   */
  kScaTriggerTypeHwGated = 0,
  /**
   * Use the fully software controlled capture trigger. If selected, the
   * configured trigger source is not relevant.
   */
  kScaTriggerTypeSw = 1,
} sca_trigger_type_t;

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
   * Peripherals using the IO_DIV4_PERI clock (UART, GPIO, I2C, SPI Dev, ...)
   */
  kScaPeripheralIoDiv4 = 1 << 7,
  /**
   * Peripherals using the IO_DIV2_PERI clock (SPI Host 1)
   */
  kScaPeripheralIoDiv2 = 1 << 8,
  /**
   * USB.
   */
  kScaPeripheralUsb = 1 << 9,
  /**
   * Peripherals using the IO_PERI clock (SPI Host 0)
   */
  kScaPeripheralIo = 1 << 10,
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
 * Select the capture trigger type.
 *
 * @param trigger_type The trigger type to select.
 */
void sca_select_trigger_type(sca_trigger_type_t trigger_type);

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
 * Seeds the software LFSR usable e.g. for key masking.
 *
 * This functions seeds the Galois XOR type LFSR with the provided seed value.
 * Note that the LFSR itself has very low diffusion.
 *
 * @param seed The new seed value.
 */
void sca_seed_lfsr(uint32_t seed);

/**
 * Steps the software LFSR usable e.g. for key masking `num_steps` times.
 *
 * This function steps the Galois XOR type LFSR n times. Note that the LFSR
 * itself has very low diffusion. To improve the statistical properties, the
 * multiple steps can be run. For example, by running 32 steps it can be
 * ensured that each state bit depends on at least two previous state bits.
 *
 * @param num_steps The number of steps to run.

 * @return The current state of the LFSR.
 */
uint32_t sca_next_lfsr(uint16_t num_steps);

/**
 * Applies a linear layer.
 *
 * This function feeds the input through a linear permutation layer. This is
 * suitable to ensure 1) that adjacent output bits of the software LFSR do not
 * go into the same S-Box (see `sca_non_linear_layer()`) and 2) that the output
 * of S-Box(n) is not always going to be equal to the output of S-Box(n+1) in
 * the subsequent cycle. For details on how this can be achieved, refer to the
 * corresponding hardware implementation in hw/ip/prim/rtl/prim_lfsr.sv.
 *
 * @param input The input value.
 *
 * @return The output of the linear layer.
 *
 */
uint32_t sca_linear_layer(uint32_t input);

/**
 * Applies a non-linear layer.
 *
 * This function feeds the input through a non-linear layer. It is suitable to
 * improve the statistical properties of the software LFSR usable for key
 * masking, see `sca_seed_lfsr()` and `sca_next_lfsr()`. Internally, a LUT-based
 * AES S-Box is applied to the invididual bytes of the input word.
 *
 * In addition, the ouput bytes are XORed with the sbox[0]. This is useful to
 * ensure an all-zero seed (used to switch off key masking) also results in an
 * all-zero output of the non-linear layer.
 *
 * @param input The input value.
 *
 * @return The output of the non-linear layer.
 *
 */
uint32_t sca_non_linear_layer(uint32_t input);

#endif  // OPENTITAN_SW_DEVICE_SCA_LIB_SCA_H_
