// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_

#include <stdint.h>

/**
 * This header contains "device-specific" declarations, i.e., information that
 * all devices are known to provide, but which is specific to the particular
 * choice of platform, which can range from a software simulation, like
 * Verilator or a DV testbench, to real harware, like an FPGA or ASIC.
 *
 * Definitions for these symbols can be found in other files in this directory,
 * which should be linked in depending on which platform an executable is
 * intended for.
 */

/**
 * A `device_type_t` represents a particular device type for which
 * device-specific symbols are available.
 */
typedef enum device_type {
  /**
   * Represents "DV", i.e. running th test in a DV simulation testbench.
   */
  kDeviceSimDV,
  /**
   * Represents the "Verilator" device, i.e., a synthesis of the OpenTitan
   * design by Verilator into C++.
   */
  kDeviceSimVerilator,
  /**
   * Represents the "Nexys Video FPGA" device, i.e., the particular FPGA board
   * blessed for OpenTitan development, containing a Xilinx FPGA.
   */
  kDeviceFpgaNexysVideo,
} device_type_t;

/**
 * Indicates the device that this program has been linked for.
 *
 * This can be used, for example, for conditioning an operation on the precise
 * device type.
 */
extern const device_type_t kDeviceType;

/**
 * The clock frequency of the device, in hertz.
 */
extern const uint64_t kClockFreqHz;

/**
 * The baudrate of the UART peripheral (if such a thing is present).
 */
extern const uint64_t kUartBaudrate;

#endif  // OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_
