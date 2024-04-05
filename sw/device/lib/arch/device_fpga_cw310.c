// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"

/**
 * @file
 * @brief Device-specific symbol definitions for the ChipWhisperer CW310 device.
 */

const device_type_t kDeviceType = kDeviceFpgaCw310;

const uint64_t kClockFreqCpuMhz = 24;

const uint64_t kClockFreqCpuHz = kClockFreqCpuMhz * 1000 * 1000;

uint64_t to_cpu_cycles(uint64_t usec) { return usec * kClockFreqCpuMhz; }

const uint64_t kClockFreqHiSpeedPeripheralHz = 24 * 1000 * 1000;  // 24MHz

const uint64_t kClockFreqPeripheralHz = 6 * 1000 * 1000;  // 6MHz

const uint64_t kClockFreqUsbHz = 48 * 1000 * 1000;  // 48MHz

const uint64_t kClockFreqAonHz = 250 * 1000;  // 250kHz

const uint64_t kUartBaudrate = 115200;

const uint32_t kUartNCOValue =
    CALCULATE_UART_NCO(kUartBaudrate, kClockFreqPeripheralHz);

const uint32_t kUartTxFifoCpuCycles =
    CALCULATE_UART_TX_FIFO_CPU_CYCLES(kUartBaudrate, kClockFreqCpuHz);

const uint32_t kAstCheckPollCpuCycles =
    CALCULATE_AST_CHECK_POLL_CPU_CYCLES(kClockFreqCpuHz);

const uintptr_t kDeviceTestStatusAddress = 0;

const uintptr_t kDeviceLogBypassUartAddress = 0;

void device_fpga_version_print(void) {
  // This value is guaranteed to be zero on all non-FPGA implementations.
  uint32_t fpga = ibex_fpga_version();
  // The cast to unsigned int stops GCC from complaining about uint32_t
  // being a `long unsigned int` while the %x specifier takes `unsigned int`.
  dbg_printf("ROM:%x\r\n", (unsigned int)fpga);
}
