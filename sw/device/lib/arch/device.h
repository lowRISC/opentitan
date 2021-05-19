// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_

#include <stdint.h>

/**
 * @file
 * @brief This header contains declarations of device-specific information.
 *
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
 * The CPU clock frequency of the device, in hertz.
 * This is the operating clock for the main processing host.
 */
extern const uint64_t kClockFreqCpuHz;

/**
 * The peripheral clock frequency of the device, in hertz.
 * This is the operating clock used by timers, uarts,
 * other peripheral interfaces and the software interface
 * to the USB controller.
 */
extern const uint64_t kClockFreqPeripheralHz;

/**
 * The USB clock frequency of the device, in hertz.
 * This is the operating clock used by the USB phy interface.
 */
extern const uint64_t kClockFreqUsbHz;

/**
 * The baudrate of the UART peripheral (if such a thing is present).
 */
extern const uint64_t kUartBaudrate;

/**
 * A helper macro to calculate NCO values.
 * NOTE: the left shift value is dependent on the UART hardware.
 * The NCO width is 16 bits and the NCO calculates a 16x oversampling clock.
 */
#define CALCULATE_UART_NCO(baudrate, peripheral_clock) \
  (((baudrate) << (16 + 4)) / (peripheral_clock))

/**
 * The pre-calculated UART NCO value based on the Baudrate and Peripheral clock.
 */
extern const uint32_t kUartNCOValue;
;

/**
 * An address to write to to report test status.
 *
 * If this is zero, there is no address to write to to report test status.
 *
 * Depending on the simulation environment and the value written to this
 * address, the simulation may stop.
 *
 * @see #test_status_set
 */
extern const uintptr_t kDeviceTestStatusAddress;

/**
 * An address to write use for UART logging bypass
 *
 * If this is zero, there is no address to write to to bypass UART logging.
 *
 * @see #LOG
 */
extern const uintptr_t kDeviceLogBypassUartAddress;

#endif  // OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_
