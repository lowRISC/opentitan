// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/json/chip_specific_startup.h"

#include <stdbool.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_sram_ctrl.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

status_t test_chip_specific_startup(ujson_t *uj) {
  dif_sram_ctrl_t sram_ctrl;

  LOG_INFO("Initializing DIFs");
  TRY(dif_sram_ctrl_init(
      mmio_region_from_addr(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR),
      &sram_ctrl));

  LOG_INFO("Querying hardware");
  dif_sram_ctrl_status_bitfield_t sram;
  TRY(dif_sram_ctrl_get_status(&sram_ctrl, &sram));

  chip_startup_t cs = {
      .ast_init_done = false,
      .sram =
          {
              .scr_key_valid = (sram & kDifSramCtrlStatusScrKeyValid) != 0,
              .scr_key_seed_valid =
                  (sram & kDifSramCtrlStatusScrKeySeedValid) != 0,
              .init_done = (sram & kDifSramCtrlStatusInitDone) != 0,
          },
  };

  RESP_OK(ujson_serialize_chip_startup_t, uj, &cs);
  return OK_STATUS();
}

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandChipStartup:
        RESP_ERR(uj, test_chip_specific_startup(uj));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  return OK_STATUS(0);
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();
  return status_ok(command_processor(&uj));
}
