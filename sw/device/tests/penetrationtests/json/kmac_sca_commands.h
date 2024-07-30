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
#define KMACSCA_CMD_MAX_DATA_BYTES 16
#define KMACSCA_CMD_MAX_KEY_BYTES 16
#define KMACSCA_CMD_MAX_LFSR_BYTES 4
#define KMACSCA_CMD_MAX_MSG_BYTES 16

// clang-format off

#define KMAC_SCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, SetKey) \
    value(_, SingleAbsorb) \
    value(_, Batch) \
    value(_, FixedKeySet) \
    value(_, SeedLfsr)
UJSON_SERDE_ENUM(KmacScaSubcommand, kmac_sca_subcommand_t, KMAC_SCA_SUBCOMMAND);

#define KMAC_SCA_KEY(field, string) \
    field(key, uint8_t, KMACSCA_CMD_MAX_KEY_BYTES) \
    field(key_length, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacScaKey, cryptotest_kmac_sca_key_t, KMAC_SCA_KEY);

#define KMAC_SCA_LFSR(field, string) \
    field(seed, uint8_t, KMACSCA_CMD_MAX_LFSR_BYTES)
UJSON_SERDE_STRUCT(CryptotestKmacScaLfsr, cryptotest_kmac_sca_lfsr_t, KMAC_SCA_LFSR);

#define KMAC_SCA_FPGA_MODE(field, string) \
    field(fpga_mode, uint8_t)
UJSON_SERDE_STRUCT(CryptotestKmacScaFpgaMode, cryptotest_kmac_sca_fpga_mode_t, KMAC_SCA_FPGA_MODE);

#define KMAC_SCA_DATA(field, string) \
    field(data, uint8_t, KMACSCA_CMD_MAX_DATA_BYTES)
UJSON_SERDE_STRUCT(CryptotestKmacScaData, cryptotest_kmac_sca_data_t, KMAC_SCA_DATA);

#define KMAC_SCA_MSG(field, string) \
    field(msg, uint8_t, KMACSCA_CMD_MAX_MSG_BYTES) \
    field(msg_length, size_t)
UJSON_SERDE_STRUCT(CryptotestKmacScaMsg, cryptotest_kmac_sca_msg_t, KMAC_SCA_MSG);

#define KMAC_SCA_BATCH_DIGEST(field, string) \
    field(batch_digest, uint8_t, KMACSCA_CMD_MAX_BATCH_DIGEST_BYTES)
UJSON_SERDE_STRUCT(CryptotestKmacScaBatchDigest, cryptotest_kmac_sca_batch_digest_t, KMAC_SCA_BATCH_DIGEST);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_KMAC_SCA_COMMANDS_H_
