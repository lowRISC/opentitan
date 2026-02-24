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

void coverage_report(void) {
  if (coverage_is_valid()) {
    base_printf("\x10== COVERAGE PROFILE START ==\r\n");
    coverage_printer_run();
    base_printf("\x10== COVERAGE PROFILE END ==\r\n");
  } else {
    base_printf("\x10== COVERAGE PROFILE INVALID ==\r\n");
  }
}

void coverage_printer_sink(const void *data, size_t size) {
  for (size_t i = 0; i < size; ++i) {
    base_printf("%02x", ((uint8_t *)data)[i]);
  }
}
