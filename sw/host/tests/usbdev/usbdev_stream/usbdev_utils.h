// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_UTILS_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_UTILS_H_
#include <cstdint>
#include <sys/types.h>

/**
 * Open and configure a serial port connection to/from the USB device.
 * The returned file descriptor may be passed directly to close()
 *
 * @param  dev_name  Device path of serial port
 * @param  bWrite    Indicates whether to open for writing or reading
 * @return           File descriptor, or negative to indicate failure
 */
int port_open(const char *dev_name, bool bWrite);

/**
 * Receive a sequence of bytes from the USB device, non-blocking
 *
 * @return           Number of bytes received, or -ve to indicate failure
 */
ssize_t recv_bytes(int in, uint8_t *buf, size_t len);

/**
 * Send a sequence of bytes to the USB device, non-blocking
 *
 * @param  out       File descriptor
 * @param  data      Data to be transmitted
 * @param  len       Number of bytes to be transmitted
 * @return           Number of bytes transmitted, or -ve to indicate failure
 */

ssize_t send_bytes(int out, const uint8_t *data, size_t len);

/**
 * Return current monotonic wall time in microsecoinds
 *
 * @return           Current time
 */
uint64_t time_us(void);

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_UTILS_H_
