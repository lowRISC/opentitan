// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "InstrProfiling.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/coverage.h"

/**
 * When the linker finds a definition of this symbol, it knows to skip loading
 * the object which contains the profiling runtime's static initializer. See
 * https://clang.llvm.org/docs/SourceBasedCodeCoverage.html#using-the-profiling-runtime-without-static-initializers
 * for more information.
 */
int __llvm_profile_runtime;

/**
 * Coverage buffer in `.bss` to avoid stack issues.
 */
static char buf[0x8000] = {0};

/**
 * Sends the given buffer as a hex string over UART.
 *
 * Lines are limited to 80 characters. Longer buffers will be broken to multiple
 * lines.
 */
void coverage_send_buffer(void) {
  // It looks like we don't have a way to read the profile buffer incrementally.
  // Thus, we define the following buffer.
  // Write the profile buffer to the buffer defined above.
  uint64_t buf_size_u64 = __llvm_profile_get_size_for_buffer();
  if (buf_size_u64 > sizeof(buf)) {
    LOG_ERROR("ERROR: LLVM profile buffer is too large: %u bytes.",
              (uint32_t)buf_size_u64);
    OT_UNREACHABLE();
  } else {
    size_t buf_size = (size_t)buf_size_u64;
    __llvm_profile_write_buffer(buf);
    // Send the buffer along with its length and CRC32.
    uint32_t checksum = crc32(buf, buf_size);
    LOG_INFO("LLVM profile data (length: %u bytes, CRC32: 0x%08x):",
             (uint32_t)buf_size, checksum);
    enum {
      kBytesPerLine = 40,
      // Print one less byte in the first line to account for "0x".
      kBytesFirstLine = kBytesPerLine - 1,
    };
    size_t bytes_this_line =
        buf_size < kBytesFirstLine ? buf_size : kBytesFirstLine;
    char *read_ptr = (char *)buf + buf_size - bytes_this_line;
    LOG_INFO("0x%!x", bytes_this_line, read_ptr);
    buf_size -= bytes_this_line;
    while (buf_size > 0) {
      size_t bytes_this_line =
          buf_size < kBytesPerLine ? buf_size : kBytesPerLine;
      read_ptr -= bytes_this_line;
      LOG_INFO("%!x", bytes_this_line, read_ptr);
      buf_size -= bytes_this_line;
    }
  }
  // Send `EOT` so that `cat` can exit. Note that this requires enabling
  // `icanon` using `stty`.
  base_printf("\x4");
  base_printf("\r\n");
}
