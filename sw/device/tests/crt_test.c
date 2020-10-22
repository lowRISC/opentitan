// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// Symbols defined in sw/device/exts/common/flash_link.ld, which we use to
// check that the CRT did what it was supposed to.
extern char _bss_start;
extern char _bss_end;
extern char _data_start;
extern char _data_end;
extern char _data_init_start;

// The addresses of the values above.
static const uintptr_t bss_start_addr = (uintptr_t)&_bss_start;
static const uintptr_t bss_end_addr = (uintptr_t)&_bss_end;
static const uintptr_t data_start_addr = (uintptr_t)&_data_start;
static const uintptr_t data_end_addr = (uintptr_t)&_data_end;
static const uintptr_t data_init_start_addr = (uintptr_t)&_data_init_start;

// Ensure that both .bss and .data are non-empty. The compiler will always keep
// these symbols, since they're volatile.
volatile char ensure_data_exists = 42;
volatile char ensure_bss_exists;

static dif_uart_t uart0;
static void init_uart(void) {
  CHECK(dif_uart_init(
            (dif_uart_params_t){
                .base_addr = mmio_region_from_addr(TOP_EARLGREY_UART_BASE_ADDR),
            },
            &uart0) == kDifUartOk,
        "failed to init UART");
  CHECK(dif_uart_configure(&uart0,
                           (dif_uart_config_t){
                               .baudrate = kUartBaudrate,
                               .clk_freq_hz = kClockFreqPeripheralHz,
                               .parity_enable = kDifUartToggleDisabled,
                               .parity = kDifUartParityEven,
                           }) == kDifUartConfigOk,
        "failed to configure UART");
  base_uart_stdout(&uart0);
}

int main(int argc, char **argv) {
  // NOTE: we cannot call any external functions until all checks of post-CRT
  // state are complete; this is to ensure that our checks are not tainted by
  // external functions.
  //
  // Among other things, this means we can't CHECK, since we can't initialize
  // UART. Thus, any critical failures are handled by returning from main.
  // To minimize the chance of things going wrong, we don't even bother placing
  // the checks in their own function.

  // Test core assumptions above the five addresses above. The test code
  // must be able to assume these all hold.
  //
  // Note that performing these comparisons on their addresses is UB, and will
  // cause this entire function to get deleted by the compiler.
  if (&_bss_start > &_bss_end || &_data_start > &_data_end) {
    // Something has gone terribly wrong and we have no hope of continuing the
    // test, so we're going to return and let the test time out.
    //
    // The best method for debugging a failure like this is to stare at an
    // instruction trace.
    return 1;
  }

  // Ensure that .bss was *actually* zeroed at the start of execution. If it
  // wasn't, we note the offset from _bss_start at which it wasn't.
  char *bss = &_bss_start;
  ptrdiff_t bss_len = &_bss_end - &_bss_start;
  int bad_bss_index = -1;
  for (int i = 0; i < bss_len; ++i) {
    if (bss[i] != 0) {
      bad_bss_index = i;
      break;
    }
  }

  // Similarly, ensure that .data has the values in the init section.
  char *data = &_data_start;
  char *data_init = &_data_init_start;
  ptrdiff_t data_len = &_data_end - &_data_start;
  int bad_data_index = -1;
  for (int i = 0; i < data_len; ++i) {
    if (data[i] != data_init[i]) {
      bad_data_index = i;
      break;
    }
  }

  // End of post-CRT checks; begin actual assertions..
  test_status_set(kTestStatusInTest);
  // Initialize the UART to enable logging for non-DV simulation platforms.
  if (kDeviceType != kDeviceSimDV) {
    init_uart();
  }

  CHECK(bss_start_addr % sizeof(uint32_t) == 0,
        "_bss_start not word-aligned: 0x%08x", bss_start_addr);
  CHECK(bss_end_addr % sizeof(uint32_t) == 0,
        "_bss_end not word-aligned: 0x%08x", bss_end_addr);
  CHECK(data_start_addr % sizeof(uint32_t) == 0,
        "_data_start not word-aligned: 0x%08x", data_start_addr);
  CHECK(data_end_addr % sizeof(uint32_t) == 0,
        "_data_end not word-aligned: 0x%08x", data_end_addr);
  CHECK(data_init_start_addr % sizeof(uint32_t) == 0,
        "_data_init_start not word-aligned: 0x%08x", data_init_start_addr);

  CHECK(bad_bss_index == -1, "found non-zero .bss byte at *0x%08x == 0x%02x",
        bss_start_addr + bad_bss_index, (uint32_t)bss[bad_bss_index]);
  CHECK(bad_data_index == -1,
        "found bad .data byte at *0x%08x == 0x%02x, expected 0x%02x",
        data_start_addr + bad_data_index, (uint32_t)data_init[bad_data_index]);

  test_status_set(kTestStatusPassed);

  // Unreachable code.
  return 1;
}
