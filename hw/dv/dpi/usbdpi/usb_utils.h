// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_USBDPI_USB_UTILS_H_
#define OPENTITAN_HW_DV_DPI_USBDPI_USB_UTILS_H_
#include <assert.h>
#include <stdint.h>
#include <stdio.h>

/**
 * Decode a PID and return its textual name, iff valid
 *
 * @param pid        Packet IDentifier to be decoded
 * @return           Textual name of PID (or "???")
 */
const char *decode_pid(uint8_t pid);

/**
 * Dump a sequence of bytes as hexadecimal and AsCII for diagnostic purposes
 *
 * @param file       Handle of output file
 * @param prefix     Optional prefix for each output line
 * @param data       First byte of data to be output
 * @param n          Number of bytes
 * @param flags      Formatting flags (reserved, SBZ)
 */
void dump_bytes(FILE *out, const char *prefix, const uint8_t *data, size_t n,
                uint32_t flags);

/**
 * Utility function that reads a 16-bit value from a byte stream in little
 * endian order, as per USB convention
 *
 * @param  dp        Pointer to first byte in stream
 * @return           Value read
 */
inline uint16_t get_le16(const uint8_t *dp) { return dp[0] | (dp[1] << 8); }

/**
 * Utility function that reads a 32-bit value from a byte stream in little
 * endian order, as per USB convention
 *
 * @param  dp        Pointer to first byte in stream
 * @return           Value read
 */
inline uint32_t get_le32(const uint8_t *dp) {
  return dp[0] | ((uint32_t)dp[1] << 8) | ((uint32_t)dp[2] << 16) |
         ((uint32_t)dp[3] << 24);
}

/**
 * Utility function that writes a 16-bit value into a byte stream in little
 * endian order, as per USB convention
 *
 * @param  dp        Pointer into stream to receive first byte
 * @param  n         Value to be written
 * @return           Pointer beyond the bytes written
 */
inline uint8_t *set_le16(uint8_t *dp, uint16_t n) {
  dp[0] = (uint8_t)n;
  dp[1] = (uint8_t)(n >> 8);
  return dp + 2;
}

/**
 * Utility function that writes a 32-bit value into a byte stream in little
 * endian order, as per USB convention
 *
 * @param  dp        Pointer into stream to receive first byte
 * @param  n         Value to be written
 * @return           Pointer beyond the bytes written
 */
inline uint8_t *set_le32(uint8_t *dp, uint32_t n) {
  dp[0] = (uint8_t)n;
  dp[1] = (uint8_t)(n >> 8);
  dp[2] = (uint8_t)(n >> 16);
  dp[3] = (uint8_t)(n >> 24);
  return dp + 4;
}

#endif  // OPENTITAN_HW_DV_DPI_USBDPI_USB_UTILS_H_
