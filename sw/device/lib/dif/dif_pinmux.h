// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"

/**
 * Pinmux connects peripheral input/output signals to the padring MIO
 * input/output signals.
 *
 * Every peripheral input signal is fed into a multiplexer, where selects
 * determine which padring MIO input or constants should be connected to it.
 *
 * Every padring MIO output signal is fed into a multiplexer, where selects
 * determine which peripheral output or constants should be connected to it.
 *
 * Please refer to `https://docs.opentitan.org/hw/ip/pinmux/doc/index.html` for
 * more information.
 *
 * It could be useful to refer to the Pad Control documentation
 * `https://docs.opentitan.org/hw/ip/padctrl/doc/` for more complete
 * understanding, as Pinmux HW is tightly coupled with Pad Control HW.
 */

/**
 * Peripheral input signal last and the Padring MIO input signal selects last.
 * `kDifPinmuxInselLast` is the last Padring MIO input signal + constants
 * (constant zero, constant one).
 */
extern const uint32_t kDifPinmuxPeripheralInLast;
extern const uint32_t kDifPinmuxInselFirstIn;
extern const uint32_t kDifPinmuxInselLast;

/**
 * Peripheral input signal connection.
 *
 * This is an unsigned 32-bit value that is at least zero and is no more than
 * the `kDifPinmuxPeripheralInLast` instantiation parameter of the `pinmux`
 * device.
 */
typedef uint32_t dif_pinmux_peripheral_in_t;

/**
 * Padring MIO input signal connection select.
 *
 * This is an unsigned 32-bit value that is at least zero and is no more than
 * the `kDifPinmuxInselLast` instantiation parameter of the `pinmux` device.
 */
typedef uint32_t dif_pinmux_insel_t;

/**
 * Padring MIO output signal last and the peripheral output signal selects
 * last. `kDifPinmuxOutselLast` is the last peripheral output signal + constants
 * (constant zero, constant one and High-Z).
 */
extern const uint32_t kDifPinmuxMioOutLast;
extern const uint32_t kDifPinmuxOutselFirstOut;
extern const uint32_t kDifPinmuxOutselLast;

/**
 * Padring MIO output signal connection.
 *
 * This is an unsigned 32-bit value that is at least zero and is no more than
 * the `kDifPinmuxMioOutLast` instantiation parameter of the `pinmux` device.
 */
typedef uint32_t dif_pinmux_mio_out_t;

/**
 * Peripheral output signal connection select.
 *
 * This is an unsigned 32-bit value that is at least zero and is no more than
 * the `kDifPinmuxOutselLast` instantiation parameter of the `pinmux` device.
 */
typedef uint32_t dif_pinmux_outsel_t;

/**
 * Pinmux instance state.
 *
 * Pinmux persistent data that is required by all the Pinmux API.
 */
typedef struct dif_pinmux {
  mmio_region_t base_addr; /**< Pinmux instance base address. */
} dif_pinmux_t;

/**
 * Pinmux generic status codes.
 *
 * These error codes can be used by any function. However if a function
 * requires additional status codes, it must define a set of status codes to
 * be used exclusively by such function.
 */
typedef enum dif_pinmux_result {
  kDifPinmuxOk = 0, /**< Success. */
  kDifPinmuxError,  /**< General error. */
  kDifPinmuxBadArg, /**< Input parameter is not valid. */
} dif_pinmux_result_t;

/**
 * Pinmux initialisation routine status codes.
 */
typedef enum dif_pinmux_init_result {
  kDifPinmuxInitOk = kDifPinmuxOk,
  kDifPinmuxInitError = kDifPinmuxError,
  kDifPinmuxInitBadArg = kDifPinmuxBadArg,
  kDifPinmuxInitLocked, /**< Peripheral registers are locked. */
} dif_pinmux_init_result_t;

/**
 * Initialises an instance of Pinmux.
 *
 * Information that must be retained, and is required to program Pinmux, shall
 * be stored in `pinmux`. When pinmux registers are locked, no register write
 * will take any effect. The only way to unlock the pinmux registers is by the
 * system reset.
 *
 * @param base_addr Base address of an instance of the Pinmux IP block
 * @param pinmux Pinmux state data.
 * @return `dif_pinmux_init_result_t`.
 */
dif_pinmux_init_result_t dif_pinmux_init(mmio_region_t base_addr,
                                         dif_pinmux_t *pinmux);

/**
 * Locks the pinmux registers.
 *
 * After the registers have been locked, they can only be unlocked by the
 * system reset.
 *
 * @param pinmux Pinmux state data.
 * @return `dif_pinmux_result_t`.
 */
dif_pinmux_result_t dif_pinmux_registers_lock(dif_pinmux_t *pinmux);

/**
 * Sets the connection between a peripheral input and a Padring MIO input.
 *
 * `peripheral_input` can be connected to any available Padring MIO input.
 *
 * @param pinmux Pinmux state data.
 * @param peripheral_in Peripheral input.
 * @param mio_in_select Padring MIO input to be connected to `peripheral_input`.
 * @return `dif_pinmux_result_t`.
 */
dif_pinmux_result_t dif_pinmux_insel_set(
    const dif_pinmux_t *pinmux, dif_pinmux_peripheral_in_t peripheral_in,
    dif_pinmux_insel_t mio_in_select);

/**
 * Sets the connection between a Padring MIO output and peripheral output.
 *
 * `mio_out` can be connected to any available `peripheral_select` output.
 *
 * @param pinmux Pinmux state data.
 * @param mio_out Padring MIO output.
 * @param peripheral_out_select Peripheral output select.
 * @return `dif_pinmux_result_t`.
 */
dif_pinmux_result_t dif_pinmux_outsel_set(
    const dif_pinmux_t *pinmux, dif_pinmux_mio_out_t mio_out,
    dif_pinmux_outsel_t peripheral_out_select);

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PINMUX_H_
