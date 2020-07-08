// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
#define OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
extern "C" {

struct uartdpi_ctx {
  char ptyname[64];
  int host;
  int device;
  char tmp_read;
};

void *uartdpi_create(const char *name);
int uartdpi_can_read(void *ctx_void);
char uartdpi_read(void *ctx_void);
void uartdpi_write(void *ctx_void, char c);
}
#endif  // OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
