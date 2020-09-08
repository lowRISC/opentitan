// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/mask_rom/mask_rom_lockdown.h"

#include "sw/device/lib/runtime/pmp.h"

// TODO - PMP region map.

bool mask_rom_lockdown_rom_ext_allow(const mask_rom_lockdown_ext_info_t *info) {
  (void)info;

  // TODO

  return false;
}

bool mask_rom_lockdown_peripherals(void) {
  // TODO

  return false;
}
