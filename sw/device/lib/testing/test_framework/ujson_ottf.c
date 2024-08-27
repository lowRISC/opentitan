// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ujson_ottf.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/ujson/ujson.h"

ujson_t ujson_ottf_console(void) {
  return ujson_init(ottf_console_get(), ottf_console_getc, ottf_console_putbuf);
}
