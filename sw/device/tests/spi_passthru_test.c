// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/json/spi_passthru.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_flow_control.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_spi_device_handle_t spid;

static status_t configure_jedec_id(ujson_t *uj, dif_spi_device_handle_t *spid) {
  config_jedec_id_t config;
  TRY(ujson_deserialize_config_jedec_id_t(uj, &config));
  dif_spi_device_flash_id_t id = {
      .device_id = config.device_id,
      .manufacturer_id = config.manufacturer_id,
      .continuation_code = config.continuation_code,
      .num_continuation_code = config.continuation_len,
  };
  TRY(dif_spi_device_set_flash_id(spid, id));
  return RESP_OK_STATUS(uj);
}

static status_t write_status_register(ujson_t *uj,
                                      dif_spi_device_handle_t *spid) {
  status_register_t sr;
  TRY(ujson_deserialize_status_register_t(uj, &sr));
  TRY(dif_spi_device_set_flash_status_registers(spid, sr.status));
  return RESP_OK_STATUS(uj);
}

static status_t read_status_register(ujson_t *uj,
                                     dif_spi_device_handle_t *spid) {
  status_register_t sr;
  dif_toggle_t addr_4b;
  TRY(dif_spi_device_get_flash_status_registers(spid, &sr.status));
  TRY(dif_spi_device_get_4b_address_mode(spid, &addr_4b));
  sr.addr_4b = addr_4b;
  RESP_OK(ujson_serialize_status_register_t, uj, &sr);
  return OK_STATUS();
}

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandSpiConfigureJedecId:
        RESP_ERR(uj, configure_jedec_id(uj, &spid));
        break;
      case kTestCommandSpiReadStatus:
        RESP_ERR(uj, read_status_register(uj, &spid));
        break;
      case kTestCommandSpiWriteStatus:
        RESP_ERR(uj, write_status_register(uj, &spid));
        break;
      default:
        LOG_ERROR("Unrecognized command: %d", command);
        RESP_ERR(uj, INVALID_ARGUMENT());
    }
  }
  // We should never reach here.
  return INTERNAL();
}

bool test_main(void) {
  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spid));

  // We want to block passthru of the first 5 read commands, corresponding to
  // ReadStatus{1,2,3}, ReadJedecID and ReadSfdp.
  // We also block all write commands.
  spi_device_testutils_configure_passthrough(&spid,
                                             /*filters=*/0x1F,
                                             /*upload_write_commands=*/true);

  dif_spi_device_passthrough_intercept_config_t passthru_cfg = {
      .status = true,
      .jedec_id = true,
      .sfdp = true,
      .mailbox = false,
  };
  CHECK_DIF_OK(
      dif_spi_device_set_passthrough_intercept_config(&spid, passthru_cfg));

  ujson_t uj = ujson_ottf_console();
  status_t s = command_processor(&uj);
  LOG_INFO("status = %r", s);
  return status_ok(s);
}
