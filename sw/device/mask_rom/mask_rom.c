// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/mask_rom/mask_rom.h"
#include "sw/device/lib/base/stdasm.h"

void mask_rom_boot(void) {
  asm volatile("unimp");
  __builtin_unreachable();
}

void mask_rom_exception_handler(void) {}

void mask_rom_nmi_handler(void) {}
