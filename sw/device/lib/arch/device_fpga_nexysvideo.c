// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"

/**
 * Device-specific symbol definitions for the Nexysvideo device.
 */

const device_type_t kDeviceType = kDeviceFpgaNexysVideo;

const uint64_t kClockFreqHz = 50 * 1000 * 1000;  // 50MHz

const uint64_t kUartBaudrate = 230400;
