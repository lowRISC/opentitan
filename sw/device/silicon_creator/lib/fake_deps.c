// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

// FIXME: this symbol is needed by runtime/print.c.  Delete this once
// we eliminate this dependency from print.c or create a local copy for
// ROM use.
int dif_uart_byte_send_polled(const void *uart, uint8_t data) { return 0; }
