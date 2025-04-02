// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/uart.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"

void device_fpga_version_print(void) {
  // This value is guaranteed to be zero on all non-FPGA implementations.
  uint32_t fpga = ibex_fpga_version();
  //                       : M O R
  const uint32_t kRom = 0x3a4d4f52;
  uart_write_imm(kRom);
  // The cast to unsigned int stops GCC from complaining about uint32_t
  // being a `long unsigned int` while the %x specifier takes `unsigned int`.
  const uint32_t kNewline = 0x0a0d;
  uart_write_hex(fpga, sizeof(fpga), kNewline);
}
