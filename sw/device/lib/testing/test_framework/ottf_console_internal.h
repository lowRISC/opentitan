// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_

#include <stdint.h>

// Defined in ottf_console.c
extern dif_gpio_t ottf_console_gpio;
extern dif_pinmux_t ottf_console_pinmux;

// Defined in ottf_console_uart.c
void ottf_console_configure_uart(ottf_console_t *console, uintptr_t base_addr);
size_t ottf_console_uart_sink(void *console, const char *buf, size_t len);
status_t ottf_console_uart_getc(void *console);
void ottf_console_uart_flow_control_enable(ottf_console_t *console, dif_rv_plic_t *plic);
status_t ottf_console_uart_flow_control(ottf_console_t *console,
                                   ottf_console_flow_control_t ctrl);

// Defined in ottf_console_spi.c
void ottf_console_configure_spi_device(ottf_console_t *console, uintptr_t base_addr);
size_t ottf_console_spi_sink(void *console, const char *buf, size_t len);
status_t ottf_console_spi_getc(void *console);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_CONSOLE_INTERNAL_H_