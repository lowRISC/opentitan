// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"

void coverage_transport_init(void) {
  ottf_console_init();
  base_printf("COV_SKIP:OTTF\r\n");
}

void coverage_init(void) {}

void coverage_report(void) { base_printf("== COVERAGE PROFILE SKIP ==\r\n"); }

void coverage_invalidate(void) {}
