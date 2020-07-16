// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"

/**
 * @file
 * @brief Device-specific symbol definitions for the Verilator device.
 */

const device_type_t kDeviceType = kDeviceSimVerilator;

const uint64_t kClockFreqHz = 500 * 1000;  // 500kHz

const uint64_t kUartBaudrate = 9600;

// Defined in `hw/top_earlgrey/top_earlgrey_verilator.core`
const uintptr_t kDeviceStopAddress = 0x10008000;
