// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
#define OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_

#ifdef __cplusplus
extern "C" {
#endif

// Set up the UART DPI and returns a context struct.
// - name: The name of the UART which will be used for the log file.
// - log_file_path: Path to where the log file should be stored.
// - exit_string: When this string is written to UART DPI the simulation will
//                exit. Exit feature is disabled when this is empty. It must
//                also be less than EXIT_STRING_MAX_LENGTH including null
//                character.
void *uartdpi_create(const char *name, const char *log_file_path,
                     const char *exit_string);
// Close all the handles held by the UART DPI and frees the context.
void uartdpi_close(void *ctx_void);
// Does a read and returns whether a valid character was read.
int uartdpi_can_read(void *ctx_void);
// Returns the last successfully read character.
char uartdpi_read(void *ctx_void);
// Writes a character (c) to the host and the log file.
// Returns non-zero when exit string has been seen.
int uartdpi_write(void *ctx_void, char c);

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // OPENTITAN_HW_DV_DPI_UARTDPI_UARTDPI_H_
