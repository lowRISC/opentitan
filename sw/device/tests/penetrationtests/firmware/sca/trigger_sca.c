// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/trigger_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/trigger_sca_commands.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Select trigger type command handler.
 *
 * This function only supports 1-byte trigger values.
 *
 * The uJSON data contains:
 *  - Source: The trigger source type.
 * @param uj The received uJSON data.
 */
status_t handle_trigger_sca_select_source(ujson_t *uj) {
  cryptotest_trigger_sca_source_t uj_trigger;
  TRY(ujson_deserialize_cryptotest_trigger_sca_source_t(uj, &uj_trigger));

  pentest_select_trigger_type(uj_trigger.source);

  return OK_STATUS();
}

status_t handle_trigger_sca_sensor_config(ujson_t *uj) {
  cryptotest_trigger_sca_sensor_cfg_t uj_cfg;
  TRY(ujson_deserialize_cryptotest_trigger_sca_sensor_cfg_t(uj, &uj_cfg));
  pentest_sensor_sca_config(uj_cfg.enable, uj_cfg.clear);
  return OK_STATUS();
}

status_t handle_trigger_sca_sensor_read_batch(ujson_t *uj) {
  cryptotest_trigger_sca_sensor_batch_t uj_batch;
  memset(&uj_batch, 0, sizeof(uj_batch));
  uint32_t count = 0;
  uint32_t total = 0;
  pentest_sensor_sca_pop_batch(TRIGGERSCA_CMD_MAX_SENSOR_SAMPLES, &count,
                               &total, uj_batch.mcycle_deltas,
                               uj_batch.clock_drift);
  uj_batch.num_samples = count;
  uj_batch.total_triggers = total;
  RESP_OK(ujson_serialize_cryptotest_trigger_sca_sensor_batch_t, uj, &uj_batch);
  return OK_STATUS();
}

status_t handle_trigger_sca(ujson_t *uj) {
  trigger_sca_subcommand_t cmd;
  TRY(ujson_deserialize_trigger_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kTriggerScaSubcommandSelectTriggerSource:
      return handle_trigger_sca_select_source(uj);
    case kTriggerScaSubcommandSensorConfig:
      return handle_trigger_sca_sensor_config(uj);
    case kTriggerScaSubcommandSensorReadBatch:
      return handle_trigger_sca_sensor_read_batch(uj);
    default:
      LOG_ERROR("Unrecognized TRIGGER SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}
