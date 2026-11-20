// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/coverage/printer.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"

void coverage_transport_init(void) {
  ottf_console_init();
  base_printf("COVERAGE:OTTF\r\n");
}

enum {
  kCoverageBatchSizeChars = 256,
};

// Batch coverage data dumps for efficiency to avoid repeated framing & host
// handshakes on every write.
static char cov_sink_buf[kCoverageBatchSizeChars];
static size_t cov_sink_len;

static void coverage_sink_flush(void) {
  if (cov_sink_len > 0) {
    base_printf("%!s", cov_sink_len, cov_sink_buf);
    cov_sink_len = 0;
  }
}

void coverage_report(void) {
  if (coverage_is_valid()) {
    base_printf("== COVERAGE PROFILE START ==\r\n");
    coverage_sink_flush();
    coverage_printer_run();
    coverage_sink_flush();
    base_printf("== COVERAGE PROFILE END ==\r\n");
  } else {
    base_printf("== COVERAGE PROFILE INVALID ==\r\n");
  }
}

void coverage_printer_sink(const void *data, size_t size) {
  for (size_t i = 0; i < size; ++i) {
    // Flush if we do not have space to print 2 more characters (i.e. 1 byte).
    if (cov_sink_len + 2 > sizeof(cov_sink_buf)) {
      coverage_sink_flush();
    }
    size_t remaining = sizeof(cov_sink_buf) - cov_sink_len;
    cov_sink_len += base_snprintf(&cov_sink_buf[cov_sink_len], remaining,
                                  "%02x", ((const uint8_t *)data)[i]);
  }
}
