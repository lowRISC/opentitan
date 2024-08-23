// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_HMAC_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_HMAC_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define HMACSCA_CMD_MAX_MESSAGE_BYTES 16
#define HMACSCA_CMD_MAX_KEY_BYTES 32
#define HMACSCA_CMD_MAX_TAG_BYTES 32

// clang-format off

#define HMACSCA_SUBCOMMAND(_, value) \
    value(_, Init) \
    value(_, BatchFvsr) \
    value(_, BatchRandom) \
    value(_, Single)
UJSON_SERDE_ENUM(HmacScaSubcommand, hmac_sca_subcommand_t, HMACSCA_SUBCOMMAND);

#define HMACSCA_MESSAGE(field, string) \
    field(message, uint8_t, HMACSCA_CMD_MAX_MESSAGE_BYTES)
UJSON_SERDE_STRUCT(PenetrationtestHmacScaMessage, penetrationtest_hmac_sca_message_t, HMACSCA_MESSAGE);

#define HMACSCA_KEY(field, string) \
    field(key, uint8_t, HMACSCA_CMD_MAX_KEY_BYTES) \
    field(mask, uint8_t, HMACSCA_CMD_MAX_KEY_BYTES)
UJSON_SERDE_STRUCT(PenetrationtestHmacScaKey, penetrationtest_hmac_sca_key_t, HMACSCA_KEY);

#define HMACSCA_TAG(field, string) \
    field(tag, uint8_t, HMACSCA_CMD_MAX_TAG_BYTES)
UJSON_SERDE_STRUCT(PenetrationtestHmacScaTag, penetrationtest_hmac_sca_tag_t, HMACSCA_TAG);

#define HMACSCA_NUM_IT(field, string) \
    field(num_iterations, uint32_t)
UJSON_SERDE_STRUCT(PenetrationtestHmacScaNumIt, penetrationtest_hmac_sca_num_it_t, HMACSCA_NUM_IT);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_HMAC_SCA_COMMANDS_H_
