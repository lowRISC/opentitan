// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/json/spi_passthru.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_emulator.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"
#include "sw/device/lib/ujson/ujson.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

volatile uint32_t kReadPipelineMode = 0;

static uint32_t current_read_pipeline_mode;
static dif_spi_device_handle_t spid;
static dif_spi_host_t spih;

static status_t configure_jedec_id(ujson_t *uj, dif_spi_device_handle_t *spid) {
  config_jedec_id_t config;
  TRY(UJSON_WITH_CRC(ujson_deserialize_config_jedec_id_t, uj, &config));
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
  TRY(UJSON_WITH_CRC(ujson_deserialize_status_register_t, uj, &sr));
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

static status_t write_sfdp_data(ujson_t *uj, dif_spi_device_handle_t *spid) {
  sfdp_data_t sfdp;
  TRY(UJSON_WITH_CRC(ujson_deserialize_sfdp_data_t, uj, &sfdp));
  TRY(dif_spi_device_write_flash_buffer(spid, kDifSpiDeviceFlashBufferTypeSfdp,
                                        0, sizeof(sfdp.data), sfdp.data));
  return RESP_OK_STATUS(uj);
}

static status_t wait_for_upload(ujson_t *uj, dif_spi_device_handle_t *spid) {
  upload_info_t info = {0};
  TRY(spi_device_testutils_wait_for_upload(spid, &info));
  // Clear the bits in flash_status to signal the end of processing of an
  // uploaded command.
  TRY(dif_spi_device_set_flash_status_registers(spid, 0));
  RESP_OK(ujson_serialize_upload_info_t, uj, &info);
  return OK_STATUS();
}

status_t spi_flash_read_id(ujson_t *uj, dif_spi_host_t *spih,
                           dif_spi_device_handle_t *spid) {
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleDisabled));
  spi_flash_testutils_jedec_id_t jedec_id;
  TRY(spi_flash_testutils_read_id(spih, &jedec_id));
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleEnabled));

  spi_flash_read_id_t uj_id = {
      .device_id = jedec_id.device_id,
      .manufacturer_id = jedec_id.manufacturer_id,
      .continuation_len = jedec_id.continuation_len,
  };
  return RESP_OK(ujson_serialize_spi_flash_read_id_t, uj, &uj_id);
}

status_t spi_flash_read_sfdp(ujson_t *uj, dif_spi_host_t *spih,
                             dif_spi_device_handle_t *spid) {
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleDisabled));
  spi_flash_read_sfdp_t op;
  TRY(UJSON_WITH_CRC(ujson_deserialize_spi_flash_read_sfdp_t, uj, &op));

  sfdp_data_t sfdp;
  CHECK(op.length <= sizeof(sfdp.data));
  TRY(spi_flash_testutils_read_sfdp(spih, op.address, sfdp.data, op.length));
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleEnabled));

  return RESP_OK(ujson_serialize_sfdp_data_t, uj, &sfdp);
}

status_t spi_flash_erase_sector(ujson_t *uj, dif_spi_host_t *spih,
                                dif_spi_device_handle_t *spid) {
  spi_flash_erase_sector_t op;
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleDisabled));
  TRY(UJSON_WITH_CRC(ujson_deserialize_spi_flash_erase_sector_t, uj, &op));
  TRY(spi_flash_testutils_erase_sector(spih, op.address, op.addr4b));
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleEnabled));
  return RESP_OK_STATUS(uj);
}

status_t spi_flash_write(ujson_t *uj, dif_spi_host_t *spih,
                         dif_spi_device_handle_t *spid) {
  spi_flash_write_t op;
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleDisabled));
  TRY(UJSON_WITH_CRC(ujson_deserialize_spi_flash_write_t, uj, &op));
  if (op.length > sizeof(op.data)) {
    LOG_ERROR("Flash write length larger than buffer: %u", op.length);
    return INVALID_ARGUMENT();
  }

  TRY(spi_flash_testutils_program_page(spih, op.data, op.length, op.address,
                                       op.addr4b));
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleEnabled));
  return RESP_OK_STATUS(uj);
}

status_t spi_mailbox_map(ujson_t *uj, dif_spi_device_handle_t *spid) {
  spi_mailbox_map_t map;
  TRY(UJSON_WITH_CRC(ujson_deserialize_spi_mailbox_map_t, uj, &map));
  TRY(dif_spi_device_enable_mailbox(spid, map.address));
  return RESP_OK_STATUS(uj);
}

status_t spi_mailbox_unmap(ujson_t *uj, dif_spi_device_handle_t *spid) {
  TRY(dif_spi_device_disable_mailbox(spid));
  return RESP_OK_STATUS(uj);
}

status_t spi_mailbox_write(ujson_t *uj, dif_spi_device_handle_t *spid) {
  spi_mailbox_write_t op;
  TRY(UJSON_WITH_CRC(ujson_deserialize_spi_mailbox_write_t, uj, &op));
  if (op.length > sizeof(op.data)) {
    LOG_ERROR("Mailbox write length larger than buffer: %u", op.length);
    return INVALID_ARGUMENT();
  }
  TRY(dif_spi_device_write_flash_buffer(spid,
                                        kDifSpiDeviceFlashBufferTypeMailbox,
                                        op.offset, op.length, op.data));
  return RESP_OK_STATUS(uj);
}

status_t spi_passthru_set_address_map(ujson_t *uj,
                                      dif_spi_device_handle_t *spid) {
  spi_passthru_swap_map_t swap;
  TRY(UJSON_WITH_CRC(ujson_deserialize_spi_passthru_swap_map_t, uj, &swap));
  TRY(dif_spi_device_set_flash_address_swap(spid, swap.mask, swap.value));
  return RESP_OK_STATUS(uj);
}

status_t command_processor(ujson_t *uj) {
  while (true) {
    test_command_t command;
    TRY(UJSON_WITH_CRC(ujson_deserialize_test_command_t, uj, &command));
    status_t result = ujson_ottf_dispatch(uj, command);
    if (status_ok(result)) {
      // Check for changes to pipeline mode.
      if (current_read_pipeline_mode != kReadPipelineMode) {
        current_read_pipeline_mode = kReadPipelineMode;
        CHECK_STATUS_OK(spi_device_testutils_configure_read_pipeline(
            &spid, current_read_pipeline_mode, current_read_pipeline_mode));
      }
      continue;
    } else if (status_err(result) != kUnimplemented) {
      return result;
    }
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
      case kTestCommandSpiWriteSfdp:
        RESP_ERR(uj, write_sfdp_data(uj, &spid));
        break;
      case kTestCommandSpiWaitForUpload:
        RESP_ERR(uj, wait_for_upload(uj, &spid));
        break;
      case kTestCommandSpiFlashReadId:
        RESP_ERR(uj, spi_flash_read_id(uj, &spih, &spid));
        break;
      case kTestCommandSpiFlashReadSfdp:
        RESP_ERR(uj, spi_flash_read_sfdp(uj, &spih, &spid));
        break;
      case kTestCommandSpiFlashEraseSector:
        RESP_ERR(uj, spi_flash_erase_sector(uj, &spih, &spid));
        break;
      case kTestCommandSpiFlashWrite:
        RESP_ERR(uj, spi_flash_write(uj, &spih, &spid));
        break;
      case kTestCommandSpiFlashEmulator:
        RESP_ERR(uj, spi_flash_emulator(&spih, &spid));
        break;
      case kTestCommandSpiMailboxMap:
        RESP_ERR(uj, spi_mailbox_map(uj, &spid));
        break;
      case kTestCommandSpiMailboxUnmap:
        RESP_ERR(uj, spi_mailbox_unmap(uj, &spid));
        break;
      case kTestCommandSpiMailboxWrite:
        RESP_ERR(uj, spi_mailbox_write(uj, &spid));
        break;
      case kTestCommandSpiPassthruSetAddressMap:
        RESP_ERR(uj, spi_passthru_set_address_map(uj, &spid));
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
  if (kDeviceType == kDeviceSilicon) {
    // On teacup board, we need to enable pull-ups on the pins connected to `WP`
    // and `HOLD`.
    dif_pinmux_t pinmux;
    mmio_region_t base_addr =
        mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
    CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux));

    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {
        .slew_rate = 1,
        .drive_strength = 3,
        .flags = kDifPinmuxPadAttrPullResistorEnable |
                 kDifPinmuxPadAttrPullResistorUp};

    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSpiHost0Sck,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSpiHost0Sd0,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSpiHost0Sd1,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));

    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSpiHost0Sd2,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));

    CHECK_DIF_OK(
        dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyDirectPadsSpiHost0Sd3,
                                   kDifPinmuxPadKindDio, in_attr, &out_attr));
  }

  const uint32_t spi_host_clock_freq_hz =
      (uint32_t)kClockFreqHiSpeedPeripheralHz;
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spih));
  dif_spi_host_config_t config = {
      .spi_clock = spi_host_clock_freq_hz / 4,
      .peripheral_clock_freq_hz = spi_host_clock_freq_hz,
      .chip_select =
          {
              .idle = 2,
              .trail = 2,
              .lead = 2,
          },
  };
  CHECK_DIF_OK(dif_spi_host_configure(&spih, config));
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(&spih, /*enabled=*/true));

  CHECK_DIF_OK(dif_spi_device_init_handle(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spid));

  // We want to block passthru of the first 5 read commands, corresponding to
  // ReadStatus{1,2,3}, ReadJedecID and ReadSfdp.
  // We also block all write commands.
  CHECK_STATUS_OK(spi_device_testutils_configure_passthrough(
      &spid,
      /*filters=*/0x1F,
      /*upload_write_commands=*/true, kWriteCommands, ARRAYSIZE(kWriteCommands),
      kReadCommands, ARRAYSIZE(kReadCommands)));

  dif_spi_device_passthrough_intercept_config_t passthru_cfg = {
      .status = true,
      .jedec_id = true,
      .sfdp = true,
      .mailbox = true,
  };
  CHECK_DIF_OK(
      dif_spi_device_set_passthrough_intercept_config(&spid, passthru_cfg));

  current_read_pipeline_mode = kReadPipelineMode;
  CHECK_STATUS_OK(spi_device_testutils_configure_read_pipeline(
      &spid, current_read_pipeline_mode, current_read_pipeline_mode));

  ujson_t uj = ujson_ottf_console();
  status_t s = command_processor(&uj);
  LOG_INFO("status = %r", s);
  return status_ok(s);
}
