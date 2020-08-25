// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"

/**
 * @file
 * @brief Device-specific symbol definitions for the Nexysvideo device.
 */

const device_type_t kDeviceType = kDeviceFpgaNexysVideo;

const uint64_t kClockFreqCpuHz = 50 * 1000 * 1000;  // 50MHz

const uint64_t kClockFreqPeripheralHz = 50 * 1000 * 1000;  // 50MHz

const uint64_t kClockFreqUsbHz = 48 * 1000 * 1000;  // 48MHz

const uint64_t kUartBaudrate = 230400;

// No Device Stop Address in our FPGA implementation.
const uintptr_t kDeviceStopAddress = 0;
