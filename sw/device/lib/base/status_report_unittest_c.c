// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/status_report_unittest_c.h"

#include "sw/device/lib/base/status.h"

/* This part of the test needs to be written in C because the TRY
 * macro is not polyglot. Specifically, the TRY macros uses
 * INTO_STATUS that relies on _Generic which is C only (although
 * the header could probably provide a different version of the
 * code for C++. */

#define MODULE_ID MAKE_MODULE_ID('g', 'o', 'd')
status_t sudo_god(void) { return PERMISSION_DENIED(); }
#undef MODULE_ID

#define MODULE_ID MAKE_MODULE_ID('p', 's', 'y')
status_t think_deeply(void) {
  TRY(sudo_god());
  return OK_STATUS();
}
#undef MODULE_ID

#define MODULE_ID MAKE_MODULE_ID('t', 'h', 'k')
status_t think(void) {
  if (!status_ok(think_deeply()))
    return ABORTED();
  return OK_STATUS();
}
#undef MODULE_ID

#define MODULE_ID MAKE_MODULE_ID('u', 'n', 't')
status_t status_report_unittest_c(void) {
  TRY(think());
  return OK_STATUS();
}
#undef MODULE_ID
