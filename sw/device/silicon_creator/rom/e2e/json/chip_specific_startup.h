// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_E2E_JSON_CHIP_SPECIFIC_STARTUP_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_E2E_JSON_CHIP_SPECIFIC_STARTUP_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

#define STRUCT_SRAM_INIT(field, string) \
    field(scr_key_valid, bool) \
    field(scr_key_seed_valid, bool) \
    field(init_done, bool)
UJSON_SERDE_STRUCT(SramInit, sram_init_t, STRUCT_SRAM_INIT);

#define STRUCT_CHIP_STARTUP(field, string) \
    field(ast_init_done, bool) \
    field(sram, sram_init_t)
UJSON_SERDE_STRUCT(ChipStartup, chip_startup_t, STRUCT_CHIP_STARTUP);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_E2E_JSON_CHIP_SPECIFIC_STARTUP_H_
