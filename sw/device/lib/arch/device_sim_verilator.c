// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>

#include "sw/device/lib/arch/device.h"

/**
 * @file
 * @brief Device-specific symbol definitions for the Verilator device.
 */

const device_type_t kDeviceType = kDeviceSimVerilator;

// Changes to the clock frequency or UART baud rate must also be reflected at
// `hw/top_earlgrey/rtl/chip_earlgrey_verilator.sv` and
// `test/systemtest/earlgrey/test_sim_verilator.py`.
#define CPU_FREQ_HZ 500 * 1000
const uint64_t kClockFreqCpuHz = CPU_FREQ_HZ;  // 500kHz

// This function is specific for the frequency above. Notice since the cycle
// time is 2 us we round up.
uint64_t to_cpu_cycles(uint64_t usec) {
  static_assert(CPU_FREQ_HZ == 500 * 1000,
                "The verilator to_cpu_cycles function needs refactoring.");
  return (usec + 1) / 2;
}

const uint64_t kClockFreqHiSpeedPeripheralHz = 500 * 1000;  // 500kHz

const uint64_t kClockFreqPeripheralHz = 125 * 1000;  // 125kHz

const uint64_t kClockFreqUsbHz = 500 * 1000;  // 500kHz

const uint64_t kClockFreqAonHz = 125 * 1000;  // 125kHz

const uint64_t kUartBaudrate = 7200;

const uint32_t kUartNCOValue =
    CALCULATE_UART_NCO(kUartBaudrate, kClockFreqPeripheralHz);

const uint32_t kUartTxFifoCpuCycles =
    CALCULATE_UART_TX_FIFO_CPU_CYCLES(kUartBaudrate, kClockFreqCpuHz);

const uint32_t kAstCheckPollCpuCycles =
    CALCULATE_AST_CHECK_POLL_CPU_CYCLES(kClockFreqCpuHz);

// Defined in `hw/top_earlgrey/chip_earlgrey_verilator.core`
const uintptr_t kDeviceTestStatusAddress = 0x411f0080;

const uintptr_t kDeviceLogBypassUartAddress = 0;

const bool kJitterEnabled = false;

void device_fpga_version_print(void) {}
