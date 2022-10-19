// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_CHIP_SPECIFIC_STARTUP_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_CHIP_SPECIFIC_STARTUP_H_

#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif
// clang-format off

// OTP words that we care about for low-level init.
#define STRUCT_ROM_OTP_CONFIG(field, string) \
    field(creator_sw_cfg_ast_init_en, uint32_t) \
    field(creator_sw_cfg_jitter_en, uint32_t)
UJSON_SERDE_STRUCT(RomOtpConfig, rom_otp_config_t, STRUCT_ROM_OTP_CONFIG);

// Configuration values from the entropy/rng IPs.
#define STRUCT_ROM_ENTROPY_CONFIG(field, string) \
    field(entropy_src, uint32_t) \
    field(csrng, uint32_t) \
    field(edn, uint32_t)
UJSON_SERDE_STRUCT(RomEntropyConfig, rom_entropy_config_t, STRUCT_ROM_ENTROPY_CONFIG);

// ePMP configuration from the ROM.
#define STRUCT_ROM_EPMP_CONFIG(field, string) \
    field(cfg, uint32_t, 4) \
    field(addr, uint32_t, 16) \
    field(mseccfg, uint32_t)
UJSON_SERDE_STRUCT(RomEpmpConfig, rom_epmp_config_t, STRUCT_ROM_EPMP_CONFIG);

// SRAM initialization values.
#define STRUCT_SRAM_INIT(field, string) \
    field(scr_key_valid, bool) \
    field(scr_key_seed_valid, bool) \
    field(init_done, bool)
UJSON_SERDE_STRUCT(SramInit, sram_init_t, STRUCT_SRAM_INIT);

#define STRUCT_CHIP_STARTUP(field, string) \
    field(otp, rom_otp_config_t) \
    field(lc_state, uint32_t) \
    field(mstatus, uint32_t) \
    field(jitter, bool) \
    field(entropy, rom_entropy_config_t) \
    field(epmp, rom_epmp_config_t) \
    field(ast_init_done, bool) \
    field(sram, sram_init_t)
UJSON_SERDE_STRUCT(ChipStartup, chip_startup_t, STRUCT_CHIP_STARTUP);

// clang-format on
#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_JSON_CHIP_SPECIFIC_STARTUP_H_
