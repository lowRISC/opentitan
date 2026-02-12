// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom_state.h"

/**
 * A dummy pre-run hook for the `kRomStateInit` ROM state.
 *
 * This is an example on how Silicon Creators should define a ROM state hook.
 */
OT_WARN_UNUSED_RESULT rom_error_t dummy_rom_init_pre_hook(void *arg) {
  return kErrorOk;
}
ROM_STATE_PRE_HOOK(kRomStateInit, dummy_rom_init_pre_hook);
