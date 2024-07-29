// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_SHA3_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_SHA3_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define SHA3SCA_CMD_MAX_BATCH_DIGEST_BYTES 32
#define SHA3SCA_CMD_MAX_DATA_BYTES 16
#define SHA3SCA_CMD_MAX_LFSR_BYTES 4
#define SHA3SCA_CMD_MAX_MSG_BYTES 16
#define SHA3SCA_CMD_MAX_STATUS_BYTES 1

// clang-format off

#define SHA3_SCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, SingleAbsorb) \
    value(_, Batch) \
    value(_, FixedMessageSet) \
    value(_, SeedLfsr) \
    value(_, DisableMasking)
UJSON_SERDE_ENUM(Sha3ScaSubcommand, sha3_sca_subcommand_t, SHA3_SCA_SUBCOMMAND);

#define SHA3_SCA_MASKS(field, string) \
    field(masks_off, uint8_t)
UJSON_SERDE_STRUCT(CryptotestSha3ScaMasks, cryptotest_sha3_sca_masks_off_t, SHA3_SCA_MASKS);

#define SHA3_SCA_LFSR(field, string) \
    field(seed, uint8_t, SHA3SCA_CMD_MAX_LFSR_BYTES)
UJSON_SERDE_STRUCT(CryptotestSha3ScaLfsr, cryptotest_sha3_sca_lfsr_t, SHA3_SCA_LFSR);

#define SHA3_SCA_DATA(field, string) \
    field(data, uint8_t, SHA3SCA_CMD_MAX_DATA_BYTES)
UJSON_SERDE_STRUCT(CryptotestSha3ScaData, cryptotest_sha3_sca_data_t, SHA3_SCA_DATA);

#define SHA3_SCA_FPGA_MODE(field, string) \
    field(fpga_mode, uint8_t)
UJSON_SERDE_STRUCT(CryptotestSha3ScaFpgaMode, cryptotest_sha3_sca_fpga_mode_t, SHA3_SCA_FPGA_MODE);

#define SHA3_SCA_MSG(field, string) \
    field(msg, uint8_t, SHA3SCA_CMD_MAX_MSG_BYTES) \
    field(msg_length, size_t)
UJSON_SERDE_STRUCT(CryptotestSha3ScaMsg, cryptotest_sha3_sca_msg_t, SHA3_SCA_MSG);

#define SHA3_SCA_STATUS(field, string) \
    field(status, uint8_t)
UJSON_SERDE_STRUCT(CryptotestSha3ScaStatus, cryptotest_sha3_sca_status_t, SHA3_SCA_STATUS);

#define SHA3_SCA_BATCH_DIGEST(field, string) \
    field(batch_digest, uint8_t, SHA3SCA_CMD_MAX_BATCH_DIGEST_BYTES)
UJSON_SERDE_STRUCT(CryptotestSha3ScaBatchDigest, cryptotest_sha3_sca_batch_digest_t, SHA3_SCA_BATCH_DIGEST);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_SHA3_SCA_COMMANDS_H_
