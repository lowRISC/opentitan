// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_XMODEM_TESTLIB_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_XMODEM_TESTLIB_H_
#include "sw/device/silicon_creator/lib/xmodem.h"

/**
 * Read data from the input within the specified timeout.
 *
 * @param iohandle An opaque user pointer associated with the io device.
 * @param data Buffer to read the data into.
 * @param len The length of the buffer.
 * @param timeout_ms The timeout.
 * @return The number of bytes actually read.
 */
size_t xmodem_read(void *iohandle, uint8_t *data, size_t len,
                   uint32_t timeout_ms);

/**
 * Write data to the output.
 *
 * @param iohandle An opaque user pointer associated with the io device.
 * @param data Buffer to write to the output.
 * @param len The length of the buffer.
 */
void xmodem_write(void *iohandle, const uint8_t *data, size_t len);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_XMODEM_TESTLIB_H_
