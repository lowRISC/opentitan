// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
#define OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_

#ifdef __cplusplus
extern "C" {
#endif

void *uartdpi_create(const char *name, const char *log_file_path);
void uartdpi_close(void *ctx_void);
int uartdpi_can_read(void *ctx_void);
char uartdpi_read(void *ctx_void);
void uartdpi_write(void *ctx_void, char c);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
