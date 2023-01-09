// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Default pinmux initialization.
 *
 * Initializes GPIOs to map to the lowest-numbered MIOs, except where it
 * conflicts with UARTs. Then initializes 2 UART mappings to (IOC3,IOC8) and
 * (IOC4,IOC9), denoted as (RX pin,TX pin).
 *
 * Also ensures IOR0 and IOR1 outputs are disabled, for use as USB sense inputs.
 *
 * This function is specific to top_earlgrey and top_englishbreakfast.
 */
void pinmux_testutils_init(dif_pinmux_t *pinmux);

/**
 * Maps the chip IOs to the GPIO peripheral in input and output directions.
 */
extern const dif_pinmux_index_t kPinmuxTestutilsGpioInselPins[kDifGpioNumPins];
extern const dif_pinmux_index_t kPinmuxTestutilsGpioMioOutPins[kDifGpioNumPins];

/**
 * Returns the mask of testable GPIO pins.
 *
 * Returns a simulation-device-specific mask that enables testing of only a
 * subset of GPIOs depending on the IO allocation limitations.
 */
uint32_t pinmux_testutils_get_testable_gpios_mask(void);

/**
 * Reads a pin as a four-valued strapping pin.
 *
 * The value returned will be in the range [0..3] and represent the following
 * values:
 *   0: Strong 0
 *   1: Weak 0
 *   2: Weak 1
 *   3: Strong 1
 *
 * @param pinmux A pinmux handle.
 * @param gpio A GPIO handle.
 * @param io The GPIO pin to read.
 * @param pad The pinmux pad to which the GPIO pin is connected.
 * @return A result in the range [0..3].
 */
uint32_t pinmux_testutils_read_strap_pin(dif_pinmux_t *pinmux, dif_gpio_t *gpio,
                                         dif_gpio_pin_t io,
                                         top_earlgrey_muxed_pads_t pad);

/**
 * Reads the OpenTitan sw strap pins for the strap configuration value.
 *
 * The value returned is the combination of 2-bit values returned from
 * [IOC2, IOC1, IOC0] and ranges from [0..63].
 * This function assumes the Earlgrey configuration where the external
 * pads IOC{0,1,2} are used as software straps and that the pinmux is
 * configured to map those pads to GPIOs 22, 23 and 24.
 *
 * @return A result in the range [0..63].
 */
uint32_t pinmux_testutils_read_straps(dif_pinmux_t *pinmux, dif_gpio_t *gpio);

/**
 * A convenience struct to associate pad attributes with a specific pad.
 */
typedef struct pinmux_pad_attributes {
  dif_pinmux_index_t pad;
  dif_pinmux_pad_kind_t kind;
  dif_pinmux_pad_attr_flags_t flags;
} pinmux_pad_attributes_t;

/**
 * Configures several pad attributes.
 */
void pinmux_testutils_configure_pads(const dif_pinmux_t *pinmux,
                                     const pinmux_pad_attributes_t *attrs,
                                     size_t num_attrs);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_PINMUX_TESTUTILS_H_
