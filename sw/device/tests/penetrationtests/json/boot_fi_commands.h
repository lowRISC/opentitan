// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_BOOT_FI_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_BOOT_FI_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

// clang-format off

#define BOOTFI_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, InactiveFirmwareInvalidate) \
    value(_, NextSlot) \
    value(_, BootStatus) \
    value(_, EpmpStatus)
C_ONLY(UJSON_SERDE_ENUM(BootFiSubcommand, boot_fi_subcommand_t, BOOTFI_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(BootFiSubcommand, boot_fi_subcommand_t, BOOTFI_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define BOOTFI_STATUS(field, string) \
    field(status, bool)
UJSON_SERDE_STRUCT(BootFiStatus, boot_fi_status_t, BOOTFI_STATUS);
// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_BOOT_FI_COMMANDS_H_
