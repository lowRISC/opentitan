// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_MASK_ROM_MASK_ROM_LOCKDOWN_H_
#define OPENTITAN_SW_DEVICE_MASK_ROM_MASK_ROM_LOCKDOWN_H_

#include <stdbool.h>
#include <stdint.h>

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// TODOs:
//   Descriptions
//   

typedef struct mask_rom_lockdown_rom_ext_info {
  uintptr_t image_start_address;
  uint32_t image_size;
  // TODO - other relevant fields:
  //        R-X region offset,
  //        ROM_EXT signature,
  //        calculated signature,
  //        ...
} mask_rom_lockdown_ext_info_t;

bool mask_rom_lockdown_rom_ext_allow(const mask_rom_lockdown_ext_info_t *info);

bool mask_rom_lockdown_peripherals(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_MASK_ROM_MASK_ROM_LOCKDOWN_H_
