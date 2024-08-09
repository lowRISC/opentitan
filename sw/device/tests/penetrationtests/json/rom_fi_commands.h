// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_ROM_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_ROM_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define ROMFI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, Read)
UJSON_SERDE_ENUM(RomFiSubcommand, rom_fi_subcommand_t, ROMFI_SUBCOMMAND);


#define ROMFI_DIGEST(field, string) \
    field(digest, uint32_t, 8) \
    field(alerts, uint32_t, 3) \
    field(err_status, uint32_t)
UJSON_SERDE_STRUCT(RomFiDigest, rom_fi_digest_t, ROMFI_DIGEST);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_ROM_FI_COMMANDS_H_
