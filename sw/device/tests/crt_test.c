// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
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

/**
 * Test that crt_section_clear correctly zeros word aligned sections.
 *
 * Sections are simulated using word aligned regions of various sizes within an
 * array.
 *
 * Does not return if the test fails.
 */
static void test_crt_section_clear(void) {
  // Function to test (symbol in the CRT assembly library).
  extern void crt_section_clear(void *start, void *end);

  // Maximum end index of target section.
  const size_t kLen = 32;

  // Section indices (start inclusive, end exclusive).
  const struct {
    size_t start;
    size_t end;
  } kTests[] = {{.start = 0, .end = 0},           {.start = 0, .end = 1},
                {.start = kLen - 1, .end = kLen}, {.start = 0, .end = kLen - 1},
                {.start = 1, .end = kLen},        {.start = 0, .end = kLen}};

  for (size_t t = 0; t < ARRAYSIZE(kTests); ++t) {
    // Set target array to non-zero values.
    uint32_t section[kLen];
    const uint32_t kVal = ~0u;
    for (size_t i = 0; i < kLen; ++i) {
      section[i] = kVal;
    }

    // Clear section of target array.
    const size_t start = kTests[t].start;
    const size_t end = kTests[t].end;
    crt_section_clear(&section[start], &section[end]);

    // Check that section was cleared.
    for (size_t i = 0; i < kLen; ++i) {
      const uint32_t expect = i >= start && i < end ? 0 : kVal;
      CHECK(section[i] == expect,
            "%s case %u: section[%u] got 0x%08x, want 0x%08x", __func__, t, i,
            section[i], expect);
    }
  }
}

/**
 * Test that crt_section_copy correctly copies data between word aligned
 * sections.
 *
 * Sections are simulated using word aligned regions of various sizes within
 * arrays.
 *
 * Does not return if the test fails.
 */
static void test_crt_section_copy(void) {
  // Function to test (symbol in the CRT assembly library).
  extern void crt_section_copy(void *start, void *end, void *source);

  // Maximum end index of target section.
  const size_t kLen = 32;

  // Section indices (start inclusive, end exclusive) and source index
  // (inclusive).
  const struct {
    size_t start;
    size_t end;
    size_t source;
  } kTests[] = {{.start = 0, .end = 0, .source = 0},
                {.start = 0, .end = 1, .source = 1},
                {.start = kLen - 1, .end = kLen, .source = 2},
                {.start = 0, .end = kLen - 1, .source = 1},
                {.start = 1, .end = kLen, .source = 1},
                {.start = 0, .end = kLen, .source = 0},
                {.start = 0, .end = kLen, .source = 0},
                {.start = 1, .end = kLen, .source = 0},
                {.start = 2, .end = kLen, .source = 0},
                {.start = 3, .end = kLen, .source = 0},
                {.start = 0, .end = kLen / 2, .source = 0},
                {.start = 1, .end = kLen / 2, .source = 0},
                {.start = 2, .end = kLen / 2, .source = 0},
                {.start = 3, .end = kLen / 2, .source = 0}};

  for (size_t t = 0; t < ARRAYSIZE(kTests); ++t) {
    // Clear target array and setup source array with known values (index + 1).
    uint32_t dst[kLen], src[kLen];
    for (size_t i = 0; i < kLen; ++i) {
      src[i] = (uint32_t)(i) + 1;
      dst[i] = 0;
    }

    // Copy section from source to target array.
    const size_t start = kTests[t].start;
    const size_t end = kTests[t].end;
    const size_t source = kTests[t].source;
    crt_section_copy(&dst[start], &dst[end], &src[source]);

    // First expected value.
    uint32_t val = (uint32_t)(source) + 1;

    // Check section was copied correctly.
    for (size_t i = 0; i < kLen; ++i) {
      const uint32_t expect = i >= start && i < end ? val++ : 0;
      CHECK(dst[i] == expect, "%s case %u: dst[%u] got 0x%08x, want 0x%08x",
            __func__, t, i, dst[i], expect);
    }
  }
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

  // Unit test CRT utility functions.
  test_crt_section_clear();
  test_crt_section_copy();

  test_status_set(kTestStatusPassed);

  // Unreachable code.
  return 1;
}
