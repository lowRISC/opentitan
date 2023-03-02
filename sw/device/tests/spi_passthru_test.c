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
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_flow_control.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static dif_spi_device_handle_t spid;

status_t configure_jedec_id(ujson_t *uj, dif_spi_device_handle_t *spid) {
  config_jedec_id_t config;
  TRY(ujson_deserialize_config_jedec_id_t(uj, &config));
  dif_spi_device_flash_id_t id = {
      .device_id = config.device_id,
      .manufacturer_id = config.manufacturer_id,
      .continuation_code = config.continuation_code,
      .num_continuation_code = config.continuation_len,
  };
  TRY(dif_spi_device_set_flash_id(spid, id));

  dif_spi_device_flash_command_t read_id = {
      .opcode = 0x9F,
      .address_type = kDifSpiDeviceFlashAddrDisabled,
      .dummy_cycles = 0,
      .payload_io_type = kDifSpiDevicePayloadIoSingle,
      .passthrough_swap_address = false,
      .payload_dir_to_host = true,
      .payload_swap_enable = false,
      .upload = false,
      .set_busy_status = false,
  };
  TRY(dif_spi_device_set_flash_command_slot(spid, 3, kDifToggleEnabled,
                                            read_id));
  return RESP_OK_STATUS(uj);
}

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(ujson_deserialize_test_command_t(uj, &command));
    switch (command) {
      case kTestCommandSpiConfigureJedecId:
        RESP_ERR(uj, configure_jedec_id(uj, &spid));
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

  dif_spi_device_config_t dev_cfg = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModePassthrough,
  };
  CHECK_DIF_OK(dif_spi_device_configure(&spid, dev_cfg));

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
