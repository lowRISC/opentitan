// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "hw/top/dt/dt_api.h"
#include "hw/top/dt/dt_sram_ctrl.h"
#include "hw/top/dt/dt_uart.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print_uart.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/status.h"

static dif_uart_t uart0;
static dif_pinmux_t pinmux;
static const dt_pinmux_t kPinmuxDt = kDtPinmuxAon;
static const dt_uart_t kUartDt = kDtUartFirst;
static const dt_sram_ctrl_t kSramCtrlDt = kDtSramCtrlMain;

static uintptr_t kSramStart;
static uintptr_t kSramEnd;

bool test_main(void) {
  // Get SRAM addresses from device table
  kSramStart = dt_sram_ctrl_memory_base(kSramCtrlDt, kDtSramCtrlMemoryRam);
  kSramEnd =
      kSramStart + dt_sram_ctrl_memory_size(kSramCtrlDt, kDtSramCtrlMemoryRam);

  if (kDeviceType != kDeviceSimDV) {
    // Configure the pinmux.
    CHECK_DIF_OK(dif_pinmux_init_from_dt(kPinmuxDt, &pinmux));
    pinmux_testutils_init(&pinmux);

    // Initialize UART.
    CHECK_DIF_OK(dif_uart_init_from_dt(kUartDt, &uart0));
    CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
    CHECK_DIF_OK(dif_uart_configure(
        &uart0, (dif_uart_config_t){
                    .baudrate = (uint32_t)kUartBaudrate,
                    .clk_freq_hz = dt_clock_frequency(
                        dt_uart_clock(kUartDt, kDtUartClockClk)),
                    .parity_enable = kDifToggleDisabled,
                    .parity = kDifUartParityEven,
                    .tx_enable = kDifToggleEnabled,
                    .rx_enable = kDifToggleEnabled,
                }));
    base_uart_stdout(&uart0);
  }

  // Read the program counter and check that we are executing from SRAM.
  uint32_t pc = 0;
  asm("auipc %[pc], 0;" : [pc] "=r"(pc));
  LOG_INFO("PC: %p, SRAM: [%p, %p)", pc, kSramStart, kSramEnd);
  CHECK(pc >= kSramStart && pc < kSramEnd, "PC is outside the main SRAM");
  if (kDeviceType == kDeviceSimDV) {
    test_status_set(kTestStatusPassed);
  }
  return true;
}

// Reference functions that the debugger may wish to call. This prevents the
// compiler from dropping them as unused functions and has the side benefit of
// preventing their includes from appearing unused.
void debugger_support_functions(void) { (void)icache_invalidate; }
