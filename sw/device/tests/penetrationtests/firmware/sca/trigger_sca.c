// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/trigger_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/sca.h"
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

  sca_select_trigger_type(uj_trigger.source);

  return OK_STATUS(0);
}

status_t handle_trigger_sca(ujson_t *uj) {
  trigger_sca_subcommand_t cmd;
  TRY(ujson_deserialize_trigger_sca_subcommand_t(uj, &cmd));
  switch (cmd) {
    case kTriggerScaSubcommandSelectTriggerSource:
      return handle_trigger_sca_select_source(uj);
      break;
    default:
      LOG_ERROR("Unrecognized TRIGGER SCA subcommand: %d", cmd);
      return INVALID_ARGUMENT();
  }
  return OK_STATUS(0);
}
