// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>

#include "sw/device/lib/arch/device.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "rv_core_ibex_regs.h"

/**
 * Device-specific symbol definitions for the DV simulation device.
 */

const device_type_t kDeviceType = kDeviceSimDV;

// TODO: DV testbench completely randomizes these. Need to add code to
// retrieve these from a preloaded memory location set by the testbench.

const uint64_t kClockFreqCpuMhz = 100;

const uint64_t kClockFreqCpuHz = kClockFreqCpuMhz * 1000 * 1000;

uint64_t to_cpu_cycles(uint64_t usec) { return usec * kClockFreqCpuMhz; }

const uint64_t kClockFreqHiSpeedPeripheralHz = 96 * 1000 * 1000;  // 96MHz

const uint64_t kClockFreqPeripheralHz = 24 * 1000 * 1000;  // 24MHz

const uint64_t kClockFreqUsbHz = 48 * 1000 * 1000;  // 48MHz

const uint64_t kClockFreqAonHz = 200 * 1000;  // 200kHz

const uint64_t kUartBaudrate = 1 * 1000 * 1000;  // 1Mbps

const uint32_t kUartNCOValue =
    CALCULATE_UART_NCO(kUartBaudrate, kClockFreqPeripheralHz);

const uint32_t kUartTxFifoCpuCycles =
    CALCULATE_UART_TX_FIFO_CPU_CYCLES(kUartBaudrate, kClockFreqCpuHz);

const uint32_t kAstCheckPollCpuCycles =
    CALCULATE_AST_CHECK_POLL_CPU_CYCLES(kClockFreqCpuHz);

const uintptr_t kDeviceTestStatusAddress =
    TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR +
    RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET;

const uintptr_t kDeviceLogBypassUartAddress =
    TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR +
    RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET + 0x04;

const bool kJitterEnabled = false;

void device_fpga_version_print(void) {}
