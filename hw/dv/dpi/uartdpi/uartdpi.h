// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
#define OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_

extern "C" {

#include <stdio.h>

struct uartdpi_ctx;

void *uartdpi_create(const char *name, int listen_port,
                     const char *log_file_path);
void uartdpi_close(void *ctx_void);
int uartdpi_can_read(void *ctx_void);
char uartdpi_read(void *ctx_void);
void uartdpi_write(void *ctx_void, char c);
}
#endif  // OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
