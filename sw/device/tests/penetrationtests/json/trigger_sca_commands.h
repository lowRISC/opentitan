// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_TRIGGER_SCA_COMMANDS_H_
#define OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_TRIGGER_SCA_COMMANDS_H_
#include "sw/device/lib/ujson/ujson_derive.h"
#ifdef __cplusplus
extern "C" {
#endif

#define TRIGGERSCA_CMD_MAX_SOURCE_BYTES 1
#define TRIGGERSCA_CMD_MAX_SENSOR_SAMPLES 64

// clang-format off

// TRIGGER SCA arguments

#define TRIGGERSCA_SUBCOMMAND(_, value) \
    value(_, SelectTriggerSource) \
    value(_, SensorConfig) \
    value(_, SensorReadBatch)
UJSON_SERDE_ENUM(TriggerScaSubcommand, trigger_sca_subcommand_t, TRIGGERSCA_SUBCOMMAND);

#define TRIGGER_SCA_SOURCE(field, string) \
    field(source, uint8_t)
UJSON_SERDE_STRUCT(CryptotestTriggerScaSource, cryptotest_trigger_sca_source_t, TRIGGER_SCA_SOURCE);

#define TRIGGER_SCA_SENSOR_CFG(field, string) \
    field(enable, bool) \
    field(clear, bool)
UJSON_SERDE_STRUCT(CryptotestTriggerScaSensorCfg, cryptotest_trigger_sca_sensor_cfg_t, TRIGGER_SCA_SENSOR_CFG);

#define TRIGGER_SCA_SENSOR_BATCH(field, string) \
    field(num_samples, uint32_t) \
    field(total_triggers, uint32_t) \
    field(mcycle_deltas, uint32_t, TRIGGERSCA_CMD_MAX_SENSOR_SAMPLES) \
    field(clock_drift, uint32_t, TRIGGERSCA_CMD_MAX_SENSOR_SAMPLES)
UJSON_SERDE_STRUCT(CryptotestTriggerScaSensorBatch, cryptotest_trigger_sca_sensor_batch_t, TRIGGER_SCA_SENSOR_BATCH);

// clang-format on

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_TESTS_PENETRATIONTESTS_JSON_TRIGGER_SCA_COMMANDS_H_
