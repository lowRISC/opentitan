// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_UTILS_H_
#define OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_UTILS_H_
#include <cstdint>
#include <cstdio>

/**
 * Open and configure a serial port connection to/from the USB device.
 * The returned file descriptor may be passed directly to close().
 *
 * @param  dev_name  Device path of serial port.
 * @param  write     Indicates whether to open for writing or reading.
 * @return           File descriptor, or negative to indicate failure.
 */
int port_open(const char *dev_name, bool write);

/**
 * Receive a sequence of bytes from the USB device, non-blocking.
 *
 * @param  in        File descriptor.
 * @param  buf       Buffer to receive data.
 * @param  len       Buffer length (= maximum number of bytes to receive).
 * @return           Number of bytes received, or -ve to indicate failure.
 */
ssize_t recv_bytes(int in, uint8_t *buf, size_t len);

/**
 * Send a sequence of bytes to the USB device, non-blocking.
 *
 * @param  out       File descriptor.
 * @param  data      Data to be transmitted.
 * @param  len       Number of bytes to be transmitted.
 * @return           Number of bytes transmitted, or -ve to indicate failure.
 */

ssize_t send_bytes(int out, const uint8_t *data, size_t len);

/**
 * Dump a sequence of bytes as hexadecimal and ASCII for diagnostic purposes.
 *
 * @param  out       Output stream.
 * @param  data      Data buffer.
 * @param  n         Number of bytes.
 */
void buffer_dump(FILE *out, const uint8_t *data, size_t n);

/**
 * Return current monotonic wall time in microseconds.
 *
 * @return           Current time.
 */
uint64_t time_us(void);

/**
 * Return microseconds elapsed since the given monotonic wall time.
 *
 * @param  start     Monotonic wall time at the start of the time interval.
 * @return           Elapsed time in microseconds.
 */
inline uint64_t elapsed_time(uint64_t start) { return time_us() - start; }

/**
 * Collect a 16-bit quantity transmitted in USB byte ordering, without
 * assuming alignment or host endianness.
 *
 * @param  p         Pointer to 2 bytes.
 * @return           The 16-bit quantity read.
 */
inline uint16_t get_le16(const uint8_t *p) { return p[0] | (p[1] << 8); }

#endif  // OPENTITAN_SW_HOST_TESTS_USBDEV_USBDEV_STREAM_USBDEV_UTILS_H_
