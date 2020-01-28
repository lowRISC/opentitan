// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"

/**
 * Device-specific symbol definitions for the Verilator device.
 */

const device_type_t kDeviceType = kDeviceSimVerilator;

const uint64_t kClockFreqHz = 500 * 1000;  // 500kHz

const uint64_t kUartBaudrate = 9600;
