// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_

#include <stdint.h>

#include "hw/top/dt/dt_api.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Enables pull-up for the specified pad.
 *
 * @param pad A MIO or DIO pad.
 * @return `kErrorOk` if the operation succeeded, a `kModulePinMux` error
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t pinmux_enable_pull_up(dt_pad_t pad);

/**
 * Enables pull-down for the specified pad.
 *
 * @param pad A MIO or DIO pad.
 * @return `kErrorOk` if the operation succeeded, a `kModulePinMux` error
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t pinmux_enable_pull_down(dt_pad_t pad);

/**
 * Disables the internal pull resistor for the specified pad.
 *
 * @param pad A MIO or DIO pad.
 * @return `kErrorOk` if the operation succeeded, a `kModulePinMux` error
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t pinmux_disable_pull(dt_pad_t pad);

/**
 * Connect a peripheral I/O to a pad.
 *
 * This will try connect a peripheral I/O to a pad. More precisely,
 * the behaviour depends on the type of the I/O and pad:
 * - If both the peripheral I/O and the pad are of MIO type, this
 *   function will configure the MIO to connect them. Depending on the
 *   direction indicated by the `dir` argument, it will connect the input,
 *   output or both. If the MIO pad is an input/output but the requested
 *   direction is only an input, the MIO output will be configured as
 *   high-Z.
 * - If both are of DIO type, this function will not do anything but
 *   it will check that this peripheral I/O is indeed directly connected
 *   to this pad.
 * - Any other combination will produce an error.
 *
 * In all cases, this function will return an error if the direction(s)
 * passed as argument are incompatible with the direction(s) of the
 * peripheral I/O and the pad.
 *
 * @param periph_io A peripheral I/O.
 * @param pad A pad.
 * @param dir Direction(s) to configure.
 * @return `kErrorOk` if the operation succeeded, a `kModulePinMux` error
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
rom_error_t pinmux_connect(dt_periph_io_t periph_io, dt_pad_t pad,
                           dt_periph_io_dir_t dir);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_PINMUX_H_
