// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef GPIODPI_H_
#define GPIODPI_H_

#include <svdpi.h>

extern "C" {

/**
 * Allocate a new GPIO DPI interface, returned as an opaque pointer.
 *
 * @param name a name to use when creating the inner FIFO.
 * @param n_bits number of bits to write in each direction; this must be at
 *        most 32 bits.
 */
void *gpiodpi_create(const char *name, int n_bits);

/**
 * Attempt to post the current GPIO state to the outside world.
 *
 * Intended to be called from SystemVerilog.
 */
void gpiodpi_device_to_host(void *ctx_void, svBitVecVal *gpio_data,
                            svBitVecVal *gpio_oe);

/**
 * Attempt to read a GPIO command from the outside world.
 *
 * The commands from the host should be a space-separated sequence of high and
 * low commands, terminated by a newline. A high command is of the form |hXX|,
 * where XX are hex digits, pulls the XXth GPIO pin high; a low command, |lXX|,
 * does the opposite. All other pins at left in an unspecified state. Invalid
 * commands are ignored.
 *
 * Intended to be called from SystemVerilog.
 * @return the values to pull the GPIO pins to.
 */
uint32_t gpiodpi_host_to_device_tick(void *ctx_void, svBitVecVal *gpio_oe);

/**
 * Relinquish resources held by a GPIO DPI interface.
 */
void gpiodpi_close(void *ctx_void);

}  // extern "C"
#endif  // GPIODPI_H_
