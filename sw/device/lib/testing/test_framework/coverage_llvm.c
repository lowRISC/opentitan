// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/coverage.h"
#include "sw/device/silicon_creator/lib/crc32.h"
#include "sw/vendor/llvm_clang_rt_profile/compiler-rt/lib/profile/InstrProfiling.h"

/**
 * When the linker finds a definition of this symbol, it knows to skip loading
 * the object which contains the profiling runtime's static initializer. See
 * https://clang.llvm.org/docs/SourceBasedCodeCoverage.html#using-the-profiling-runtime-without-static-initializers
 * for more information.
 */
int __llvm_profile_runtime;

/**
 * Sends the given buffer as a hex string over UART.
 */
static void send_buffer(uint8_t *buf, size_t len) {
  for (uint32_t i = 0; i < len; ++i) {
    base_printf("%02X", buf[i]);
  }
}

void coverage_send_buffer(void) {
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
  base_printf("\x4");
}
