// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_AES_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_AES_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define AESSCA_CMD_MAX_MSG_BYTES 16
#define AESSCA_CMD_MAX_KEY_BYTES 16
#define AESSCA_CMD_MAX_LFSR_BYTES 4
#define AESSCA_CMD_MAX_DATA_BYTES 16

// clang-format off

// AES SCA arguments

#define AESSCA_SUBCOMMAND(_, value) \
    value(_, BatchAlternativeEncrypt) \
    value(_, BatchEncrypt) \
    value(_, BatchEncryptRandom) \
    value(_, BatchPlaintextSet) \
    value(_, FvsrDataBatchEncrypt) \
    value(_, FvsrKeyBatchEncrypt) \
    value(_, FvsrKeyBatchGenerate) \
    value(_, FvsrKeySet) \
    value(_, FvsrKeyStartBatchGenerate) \
    value(_, Init) \
    value(_, KeySet) \
    value(_, SeedLfsr) \
    value(_, SeedLfsrOrder) \
    value(_, SingleEncrypt)
UJSON_SERDE_ENUM(AesScaSubcommand, aes_sca_subcommand_t, AESSCA_SUBCOMMAND);

#define AES_SCA_KEY(field, string) \
    field(key, uint8_t, AESSCA_CMD_MAX_KEY_BYTES) \
    field(key_length, size_t)
UJSON_SERDE_STRUCT(CryptotestAesScaKey, aes_sca_key_t, AES_SCA_KEY);

#define AES_SCA_DATA(field, string) \
    field(data, uint8_t, AESSCA_CMD_MAX_DATA_BYTES)
UJSON_SERDE_STRUCT(CryptotestAesScaData, aes_sca_data_t, AES_SCA_DATA);

#define AES_SCA_TEXT(field, string) \
    field(text, uint8_t, AESSCA_CMD_MAX_DATA_BYTES) \
    field(text_length, size_t)
UJSON_SERDE_STRUCT(CryptotestAesScaText, aes_sca_text_t, AES_SCA_TEXT);

#define AES_SCA_LFSR(field, string) \
    field(seed, uint8_t, AESSCA_CMD_MAX_LFSR_BYTES)
UJSON_SERDE_STRUCT(CryptotestAesScaLfsr, aes_sca_lfsr_t, AES_SCA_LFSR);

#define AES_SCA_CIPHERTEXT(field, string) \
    field(ciphertext, uint8_t, AESSCA_CMD_MAX_MSG_BYTES) \
    field(ciphertext_length, uint32_t)
UJSON_SERDE_STRUCT(CryptotestAesScaCiphertext, aes_sca_ciphertext_t, AES_SCA_CIPHERTEXT);

#define AES_SCA_FPGA_MODE(field, string) \
    field(fpga_mode, uint8_t)
UJSON_SERDE_STRUCT(CryptotestAesScaFpgaMode, aes_sca_fpga_mode_t, AES_SCA_FPGA_MODE);
// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_AES_SCA_COMMANDS_H_
