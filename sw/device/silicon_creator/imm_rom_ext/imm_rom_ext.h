// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_IMM_ROM_EXT_IMM_ROM_EXT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_IMM_ROM_EXT_IMM_ROM_EXT_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

void imm_rom_ext_main(uint32_t hash_enforcement);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_IMM_ROM_EXT_IMM_ROM_EXT_H_
