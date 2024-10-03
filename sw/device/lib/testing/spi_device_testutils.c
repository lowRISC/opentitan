// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_device_testutils.h"

#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/testing/test_framework/check.h"

#define MODULE_ID MAKE_MODULE_ID('s', 'd', 't')

status_t spi_device_testutils_configure_passthrough(
    dif_spi_device_handle_t *spi_device, uint32_t filters,
    bool upload_write_commands,
    const dif_spi_device_flash_command_t *write_cmds, size_t write_cmds_size,
    const dif_spi_device_flash_command_t *read_cmds, size_t read_cmds_size) {
  dif_spi_device_config_t spi_device_config = {
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModePassthrough,
  };
  TRY(dif_spi_device_configure(spi_device, spi_device_config));

  dif_spi_device_passthrough_intercept_config_t intercept_config = {
      .status = upload_write_commands,
      .jedec_id = false,
      .sfdp = false,
      .mailbox = false,
  };
  TRY(dif_spi_device_set_passthrough_intercept_config(spi_device,
                                                      intercept_config));

  // Set up passthrough filter to allow all commands, initially.
  TRY(dif_spi_device_set_all_passthrough_command_filters(spi_device,
                                                         kDifToggleDisabled));

  for (uint8_t i = 0; i < read_cmds_size; ++i) {
    uint8_t slot = i + kSpiDeviceReadCommandSlotBase;
    if (bitfield_bit32_read(filters, slot)) {
      TRY(dif_spi_device_set_passthrough_command_filter(
          spi_device, read_cmds[i].opcode, kDifToggleEnabled));
    }
    TRY(dif_spi_device_set_flash_command_slot(spi_device, slot,
                                              kDifToggleEnabled, read_cmds[i]));
  }
  for (uint8_t i = 0; i < write_cmds_size; ++i) {
    dif_spi_device_flash_command_t cmd = write_cmds[i];
    cmd.upload = cmd.set_busy_status = upload_write_commands;
    uint8_t slot = i + (uint8_t)kSpiDeviceWriteCommandSlotBase;
    if (bitfield_bit32_read(filters, slot) || upload_write_commands) {
      TRY(dif_spi_device_set_passthrough_command_filter(spi_device, cmd.opcode,
                                                        kDifToggleEnabled));
    }
    TRY(dif_spi_device_set_flash_command_slot(spi_device, slot,
                                              kDifToggleEnabled, cmd));
  }
  // This configuration for these commands does not guard against misbehaved
  // hosts. The timing of any of these commands relative to an uploaded command
  // cannot be determined.
  TRY(dif_spi_device_configure_flash_wren_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpWriteEnable));
  TRY(dif_spi_device_configure_flash_wrdi_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpWriteDisable));
  TRY(dif_spi_device_configure_flash_en4b_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpEnter4bAddr));
  TRY(dif_spi_device_configure_flash_ex4b_command(spi_device, kDifToggleEnabled,
                                                  kSpiDeviceFlashOpExit4bAddr));

  if (upload_write_commands) {
    TRY(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpReadStatus1, kDifToggleEnabled));
    TRY(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpReadStatus2, kDifToggleEnabled));
    TRY(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpReadStatus3, kDifToggleEnabled));
    TRY(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpWriteEnable, kDifToggleEnabled));
    TRY(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpWriteDisable, kDifToggleEnabled));
  }
  return OK_STATUS();
}

status_t spi_device_testutils_configure_read_pipeline(
    dif_spi_device_handle_t *spi_device,
    dif_spi_device_read_pipeline_mode_t dual_mode,
    dif_spi_device_read_pipeline_mode_t quad_mode) {
  if (spi_device == NULL || dual_mode >= kDifSpiDeviceReadPipelineModeCount ||
      quad_mode >= kDifSpiDeviceReadPipelineModeCount) {
    return INVALID_ARGUMENT();
  }

  const dif_spi_device_flash_command_t dual_read_cmd = {
      // Slot 7: ReadDual
      .opcode = kSpiDeviceFlashOpReadDual,
      .address_type = kDifSpiDeviceFlashAddrCfg,
      .passthrough_swap_address = true,
      .dummy_cycles = 8,
      .payload_io_type = kDifSpiDevicePayloadIoDual,
      .payload_dir_to_host = true,
      .read_pipeline_mode = dual_mode,
  };
  const dif_spi_device_flash_command_t quad_read_cmd = {
      // Slot 8: ReadQuad
      .opcode = kSpiDeviceFlashOpReadQuad,
      .address_type = kDifSpiDeviceFlashAddrCfg,
      .passthrough_swap_address = true,
      .dummy_cycles = 8,
      .payload_io_type = kDifSpiDevicePayloadIoQuad,
      .payload_dir_to_host = true,
      .read_pipeline_mode = quad_mode,
  };
  TRY(dif_spi_device_set_flash_command_slot(spi_device, /*slot=*/7,
                                            kDifToggleEnabled, dual_read_cmd));
  TRY(dif_spi_device_set_flash_command_slot(spi_device, /*slot=*/8,
                                            kDifToggleEnabled, quad_read_cmd));
  return OK_STATUS();
}

status_t spi_device_testutils_configure_pad_attrs(dif_pinmux_t *pinmux) {
  dif_pinmux_pad_attr_t out_attr;
  dif_pinmux_pad_attr_t in_attr = {.slew_rate = 1, .drive_strength = 3};
  dif_result_t res;
  for (uint32_t i = 0; i <= ARRAYSIZE(spi_device_direct_pads); ++i) {
    res = dif_pinmux_pad_write_attrs(pinmux, spi_device_direct_pads[i],
                                     kDifPinmuxPadKindDio, in_attr, &out_attr);
    if (res == kDifError) {
      // Some target platforms may not support the specified value for slew rate
      // and drive strength. If that's the case, use the values actually
      // supported.
      if (out_attr.slew_rate != in_attr.slew_rate) {
        LOG_INFO(
            "Specified slew rate not supported, trying supported slew rate");
        in_attr.slew_rate = out_attr.slew_rate;
      }
      if (out_attr.drive_strength != in_attr.drive_strength) {
        LOG_INFO(
            "Specified drive strength not supported, trying supported drive "
            "strength");
        in_attr.drive_strength = out_attr.drive_strength;
      }
      TRY(dif_pinmux_pad_write_attrs(pinmux, spi_device_direct_pads[i],
                                     kDifPinmuxPadKindDio, in_attr, &out_attr));
      // Note: fallthrough with the modified `in_attr` so that the same
      // attributes are used for all pads.
    }
  }
  return OK_STATUS();
}

status_t spi_device_testutils_wait_for_upload(dif_spi_device_handle_t *spid,
                                              upload_info_t *info) {
  // Wait for a SPI transaction cause an upload.
  bool upload_pending;
  do {
    // The UploadCmdfifoNotEmpty interrupt status is updated after the SPI
    // transaction completes.
    TRY(dif_spi_device_irq_is_pending(
        &spid->dev, kDifSpiDeviceIrqUploadCmdfifoNotEmpty, &upload_pending));
  } while (!upload_pending);

  uint8_t occupancy;

  // Get the SPI opcode.
  TRY(dif_spi_device_get_flash_command_fifo_occupancy(spid, &occupancy));
  if (occupancy != 1) {
    // Cannot have an uploaded command without an opcode.
    return INTERNAL();
  }
  TRY(dif_spi_device_pop_flash_command_fifo(spid, &info->opcode));
  // Get the flash_status register.
  TRY(dif_spi_device_get_flash_status_registers(spid, &info->flash_status));

  // Get the SPI address (if available).
  TRY(dif_spi_device_get_flash_address_fifo_occupancy(spid, &occupancy));
  if (occupancy) {
    dif_toggle_t addr_4b;
    TRY(dif_spi_device_get_4b_address_mode(spid, &addr_4b));
    info->addr_4b = addr_4b;
    TRY(dif_spi_device_pop_flash_address_fifo(spid, &info->address));
    info->has_address = true;
  }

  // Get the SPI data payload (if available).
  uint32_t start;
  TRY(dif_spi_device_get_flash_payload_fifo_occupancy(spid, &info->data_len,
                                                      &start));
  if (info->data_len) {
    if (info->data_len > sizeof(info->data)) {
      // We aren't expecting more than 256 bytes of data.
      return INVALID_ARGUMENT();
    }
    TRY(dif_spi_device_read_flash_payload_buffer(spid, start, info->data_len,
                                                 info->data));
  }

  // Finished: ack the IRQ.
  TRY(dif_spi_device_irq_acknowledge(&spid->dev,
                                     kDifSpiDeviceIrqUploadCmdfifoNotEmpty));
  return OK_STATUS();
}
