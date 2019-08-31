// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef UARTDPI_H_
#define UARTDPI_H_
extern "C" {

struct uartdpi_ctx {
  char ptyname[64];
  int master;
  int slave;
  char tmp_read;
};

void *uartdpi_create(const char *name);
int uartdpi_can_read(void *ctx_void);
char uartdpi_read(void *ctx_void);
void uartdpi_write(void *ctx_void, char c);
}
#endif  // UARTDPI_H_
