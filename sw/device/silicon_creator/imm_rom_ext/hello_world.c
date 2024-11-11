// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/imm_rom_ext/hello_world.h"

#include "sw/device/silicon_creator/lib/drivers/uart.h"

void imm_rom_ext_main(void) {
  // Print "Immutable" to the UART console.
  //                        l b a t u m m I
  const uint64_t kStr1 = 0x6c626174756d6d49;
  //                        e
  const uint32_t kStr2 = 0x65;
  const uint32_t kNewline = 0x0a0d;
  uart_write_imm(kStr1);
  uart_write_imm(kStr2);
  uart_write_imm(kNewline);

  // Wait until the UART is done transmitting.
  while (!uart_tx_idle()) {
  }

  return;
}
