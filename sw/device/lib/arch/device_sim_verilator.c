// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
const uint64_t kClockFreqCpuHz = 500 * 1000;  // 500kHz

const uint64_t kClockFreqPeripheralHz = 125 * 1000;  // 125kHz

const uint64_t kClockFreqUsbHz = 500 * 1000;  // 500kHz

const uint64_t kClockFreqAonHz = 125 * 1000;  // 125kHz

const uint64_t kUartBaudrate = 7200;

const uint32_t kUartNCOValue =
    CALCULATE_UART_NCO(kUartBaudrate, kClockFreqPeripheralHz);

const uint32_t kUartTxFifoCpuCycles =
    CALCULATE_UART_TX_FIFO_CPU_CYCLES(kUartBaudrate, kClockFreqCpuHz);

// Defined in `hw/top_earlgrey/chip_earlgrey_verilator.core`
const uintptr_t kDeviceTestStatusAddress = 0x411f0080;

const uintptr_t kDeviceLogBypassUartAddress = 0;

const bool kJitterEnabled = false;
