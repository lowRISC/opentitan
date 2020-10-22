// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_coverage.h"
#include <stdint.h>
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/uart.h"
#include "sw/vendor/llvm_clang_rt_profile/compiler-rt/lib/profile/InstrProfiling.h"

/**
 * When the linker finds a definition of this symbol, it knows to skip loading
 * the object which contains the profiling runtime's static initializer. See
 * https://clang.llvm.org/docs/SourceBasedCodeCoverage.html#using-the-profiling-runtime-without-static-initializers
 * for more information.
 */
int __llvm_profile_runtime;

/**
 * Computes the CRC32 of a buffer as expected by Python's `zlib.crc32()`. The
 * implementation below is basically a simplified, i.e. byte-by-byte and without
 * a lookup table, version of zlib's crc32. See
 * https://github.com/madler/zlib/blob/2fa463bacfff79181df1a5270fb67cc679a53e71/crc32.c,
 * lines 111-112 and 276-279.
 */
static uint32_t crc32(uint8_t *buf, size_t len) {
  // CRC32 polynomial.
  static const uint32_t kPoly = 0xEDB88320;
  // Since we use a contiguous buffer, we don't need to call this function
  // multiple times. That's why `crc` is not a parameter and is initialized to
  // `UINT32_MAX`, i.e. `~0`.
  uint32_t crc = UINT32_MAX;
  for (size_t i = 0; i < len; ++i) {
    crc ^= buf[i];
    for (uint8_t j = 0; j < 8; ++j) {
      bool lsb = crc & 1;
      crc >>= 1;
      if (lsb) {
        crc ^= kPoly;
      }
    }
  }
  return ~crc;
}

/**
 * Sends the given buffer as a hex string over UART.
 */
static void send_buffer(uint8_t *buf, size_t len) {
  for (uint32_t i = 0; i < len; ++i) {
    base_printf("%2X", buf[i]);
  }
}

void test_coverage_send_buffer(void) {
  // It looks like we don't have a way to read the profile buffer incrementally.
  // Thus, we define the following buffer.
  uint8_t buf[8192] = {0};
  // Write the profile buffer to the buffer defined above.
  uint32_t buf_size = (uint32_t)__llvm_profile_get_size_for_buffer();
  if (buf_size > sizeof(buf)) {
    LOG_ERROR("ERROR: LLVM profile buffer is too large: %u bytes.", buf_size);
  } else {
    __llvm_profile_write_buffer((char *)buf);
    // Send the buffer along with its length and CRC32.
    base_printf("\r\nLLVM profile data (length: %u, CRC32: ", buf_size);
    uint32_t checksum = crc32(buf, buf_size);
    send_buffer((uint8_t *)&checksum, sizeof(checksum));
    base_printf("):\r\n");
    send_buffer(buf, buf_size);
    base_printf("\r\n");
  }
  // Send `EOT` so that `cat` can exit. Note that this requires enabling
  // `icanon` using `stty`.
  uart_send_char(4);
}
