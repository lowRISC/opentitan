// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

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
   * Represents "DV", i.e. running the test in a DV simulation testbench.
   *
   * DISCLAIMER: it is important this value remains assigned to 0, as it is
   * implicitly checked in the `test_rom_start.S` assembly code to determine
   * whether or not to initialize SRAM.
   */
  kDeviceSimDV = 0,
  /**
   * Represents the "Verilator" device, i.e., a synthesis of the OpenTitan
   * design by Verilator into C++.
   */
  kDeviceSimVerilator = 1,
  /**
   * Represents the "ChipWhisperer CW310 FPGA" device, i.e., the particular
   * FPGA board blessed for OpenTitan development, containing a Xilinx FPGA.
   */
  kDeviceFpgaCw310 = 2,
  /**
   * Represents the "ChipWhisperer CW305 FPGA" device, i.e., the smaller FPGA
   * development board with SCA capability, containing a Xilinx FPGA.
   */
  kDeviceFpgaCw305 = 3,
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
 * other peripheral interfaces.
 */
extern const uint64_t kClockFreqPeripheralHz;

/**
 * The high-speed peripheral clock frequency of the device, in hertz.
 * This is the operating clock used by the spi host
 */
extern const uint64_t kClockFreqHiSpeedPeripheralHz;

/**
 * The USB clock frequency of the device, in hertz.
 * This is the operating clock used by the USB phy interface and USB's software
 * interface.
 */
extern const uint64_t kClockFreqUsbHz;

/**
 * The always on clock frequency of the device, in hertz.
 * This is the operating clock used by the always on timer,
 * power manager and other peripherals that continue to
 * operate after the device is in sleep state.
 */
extern const uint64_t kClockFreqAonHz;

/**
 * The baudrate of the UART peripheral (if such a thing is present).
 */
extern const uint64_t kUartBaudrate;

/**
 * A helper macro to calculate NCO values.
 * NOTE: the left shift value is dependent on the UART hardware.
 * The NCO width is 16 bits and the NCO calculates a 16x oversampling clock.
 * If uart baud rate is 1.5Mbps and IO is 24Mhz, NCO is 0x10000, which is over
 * the NCO width, use NCO = 0xffff for this case since the error is tolerable.
 * Refer to #4263
 */
#define CALCULATE_UART_NCO(baudrate, peripheral_clock)  \
  (baudrate == 1500000 && peripheral_clock == 24000000) \
      ? 0xffff                                          \
      : (((baudrate) << (16 + 4)) / (peripheral_clock))

/**
 * The pre-calculated UART NCO value based on the Baudrate and Peripheral clock.
 */
extern const uint32_t kUartNCOValue;

/**
 * Helper macro to calculate the time it takes to transmit the entire UART TX
 * FIFO in CPU cycles.
 *
 * This macro assumes 10 bits per byte (no parity bits) and a 128 byte deep TX
 * FIFO.
 */
#define CALCULATE_UART_TX_FIFO_CPU_CYCLES(baud_rate_, cpu_freq_) \
  ((cpu_freq_)*10 * 128 / (baud_rate_))

/**
 * The time it takes to transmit the entire UART TX fifo in CPU cycles.
 */
extern const uint32_t kUartTxFifoCpuCycles;

/**
 * Helper macro to calculate the maximum duration of the AST initialization
 * check poll in CPU cycles.
 *
 * This macro assumes that the desired duration is 100us.
 */
#define CALCULATE_AST_CHECK_POLL_CPU_CYCLES(cpu_freq_) \
  ((cpu_freq_)*100 / 1000000)

/**
 * Maximum duration of the AST initialization check poll in CPU cycles. This
 * number depends on `kClockFreqCpuHz` and the resulting duration must be 100us.
 */
extern const uint32_t kAstCheckPollCpuCycles;

/**
 * An address to write to report test status.
 *
 * If this is zero, there is no address to write to report test status.
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
 * If this is zero, there is no address to write to bypass UART logging.
 *
 * @see #LOG
 */
extern const uintptr_t kDeviceLogBypassUartAddress;

/**
 * A knob to set jitter_enable in clkmgr.
 */
extern const bool kJitterEnabled;

/**
 * A platform-specific function to convert microseconds to cpu cycles.
 *
 * This is primarily used for spin waits that use the cpu cycle counters.
 * For platforms with clock periods slower than 1 us this will round up.
 */
uint64_t to_cpu_cycles(uint64_t usec);

/**
 * Prints the FPGA version.
 *
 * This function is a NOP unless we are building for an FPGA.
 */
void device_fpga_version_print(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_ARCH_DEVICE_H_
