// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_KMAC_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_KMAC_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define KMACSCA_CMD_MAX_BATCH_DIGEST_BYTES 32
#define KMACSCA_CMD_MAX_DIGEST_BYTES 16
#define KMACSCA_CMD_MAX_DATA_BYTES 128
#define KMACSCA_CMD_MAX_KEY_BYTES 32
#define KMACSCA_CMD_MAX_LFSR_BYTES 4
#define KMACSCA_CMD_MAX_MSG_BYTES 128

// clang-format off

#define KMAC_SCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, SetKey) \
    value(_, SingleAbsorb) \
    value(_, Batch) \
    value(_, BatchDaisy) \
    value(_, FixedKeySet) \
    value(_, SeedLfsr)
C_ONLY(UJSON_SERDE_ENUM(KmacScaSubcommand, kmac_sca_subcommand_t, KMAC_SCA_SUBCOMMAND));
RUST_ONLY(UJSON_SERDE_ENUM(KmacScaSubcommand, kmac_sca_subcommand_t, KMAC_SCA_SUBCOMMAND, RUST_DEFAULT_DERIVE, strum::EnumString));

#define KMAC_SCA_LFSR(field, string) \
    field(seed, uint8_t, KMACSCA_CMD_MAX_LFSR_BYTES)
UJSON_SERDE_STRUCT(KmacScaLfsr, kmac_sca_lfsr_t, KMAC_SCA_LFSR);

#define KMAC_SCA_FPGA_MODE(field, string) \
    field(fpga_mode, uint8_t)
UJSON_SERDE_STRUCT(KmacScaFpgaMode, kmac_sca_fpga_mode_t, KMAC_SCA_FPGA_MODE);

#define KMAC_SCA_IN(field, string) \
    field(msg, uint8_t, KMACSCA_CMD_MAX_MSG_BYTES) \
    field(msg_length, size_t) \
    field(key, uint8_t, KMACSCA_CMD_MAX_KEY_BYTES) \
    field(key_length, size_t) \
    field(customization, uint8_t, KMACSCA_CMD_MAX_MSG_BYTES) \
    field(customization_length, size_t)
UJSON_SERDE_STRUCT(KmacScaIn, kmac_sca_in_t, KMAC_SCA_IN);

#define KMAC_SCA_DIGEST(field, string) \
    field(digest, uint8_t, KMACSCA_CMD_MAX_DIGEST_BYTES)
UJSON_SERDE_STRUCT(KmacScaDigest, kmac_sca_digest_t, KMAC_SCA_DIGEST);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_KMAC_SCA_COMMANDS_H_
