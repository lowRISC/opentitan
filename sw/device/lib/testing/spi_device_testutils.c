// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_device_testutils.h"

#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/testing/test_framework/check.h"

void spi_device_testutils_configure_passthrough(
    dif_spi_device_handle_t *spi_device, uint32_t filters,
    bool upload_write_commands) {
  dif_spi_device_config_t spi_device_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModePassthrough,
  };
  CHECK_DIF_OK(dif_spi_device_configure(spi_device, spi_device_config));

  // Zero-init the payload memory to avoid X-triggered assertions in sim.
  uint8_t zeroes[256];
  memset(zeroes, 0, sizeof(zeroes));
  CHECK_DIF_OK(dif_spi_device_write_flash_buffer(
      spi_device, kDifSpiDeviceFlashBufferTypePayload, 0, sizeof(zeroes),
      zeroes));

  dif_spi_device_passthrough_intercept_config_t intercept_config = {
      .status = upload_write_commands,
      .jedec_id = false,
      .sfdp = false,
      .mailbox = false,
  };
  CHECK_DIF_OK(dif_spi_device_set_passthrough_intercept_config(
      spi_device, intercept_config));

  // Set up passthrough filter to allow all commands, initially.
  CHECK_DIF_OK(dif_spi_device_set_all_passthrough_command_filters(
      spi_device, kDifToggleDisabled));

  dif_spi_device_flash_command_t read_commands[] = {
      {
          // Slot 0: ReadStatus1
          .opcode = kSpiDeviceFlashOpReadStatus1,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 1: ReadStatus2
          .opcode = kSpiDeviceFlashOpReadStatus2,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 2: ReadStatus3
          .opcode = kSpiDeviceFlashOpReadStatus3,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 3: ReadJedecID
          .opcode = kSpiDeviceFlashOpReadJedec,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 4: ReadSfdp
          .opcode = kSpiDeviceFlashOpReadSfdp,
          .address_type = kDifSpiDeviceFlashAddr3Byte,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 5: ReadNormal
          .opcode = kSpiDeviceFlashOpReadNormal,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 6: ReadFast
          .opcode = kSpiDeviceFlashOpReadFast,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 7: ReadDual
          .opcode = kSpiDeviceFlashOpReadDual,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoDual,
          .payload_dir_to_host = true,
      },
      {
          // Slot 8: ReadQuad
          .opcode = kSpiDeviceFlashOpReadQuad,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .passthrough_swap_address = true,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoQuad,
          .payload_dir_to_host = true,
      },
  };
  for (int i = 0; i < ARRAYSIZE(read_commands); ++i) {
    uint8_t slot = i + kSpiDeviceReadCommandSlotBase;
    if (bitfield_bit32_read(filters, slot)) {
      CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
          spi_device, read_commands[i].opcode, kDifToggleEnabled));
    }
    CHECK_DIF_OK(dif_spi_device_set_flash_command_slot(
        spi_device, slot, kDifToggleEnabled, read_commands[i]));
  }
  dif_spi_device_flash_command_t write_commands[] = {
      {
          // Slot 11: WriteStatus1
          .opcode = kSpiDeviceFlashOpWriteStatus1,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 12: WriteStatus2
          .opcode = kSpiDeviceFlashOpWriteStatus2,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 13: WriteStatus3
          .opcode = kSpiDeviceFlashOpWriteStatus3,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 14: ChipErase
          .opcode = kSpiDeviceFlashOpChipErase,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 15: SectorErase
          .opcode = kSpiDeviceFlashOpSectorErase,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 16: PageProgram
          .opcode = kSpiDeviceFlashOpPageProgram,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
  };
  for (int i = 0; i < ARRAYSIZE(write_commands); ++i) {
    uint8_t slot = i + kSpiDeviceWriteCommandSlotBase;
    if (bitfield_bit32_read(filters, slot) || upload_write_commands) {
      CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
          spi_device, write_commands[i].opcode, kDifToggleEnabled));
    }
    CHECK_DIF_OK(dif_spi_device_set_flash_command_slot(
        spi_device, slot, kDifToggleEnabled, write_commands[i]));
  }
  // This configuration for these commands does not guard against misbehaved
  // hosts. The timing of any of these commands relative to an uploaded command
  // cannot be determined.
  CHECK_DIF_OK(dif_spi_device_configure_flash_wren_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpWriteEnable));
  CHECK_DIF_OK(dif_spi_device_configure_flash_wrdi_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpWriteDisable));
  CHECK_DIF_OK(dif_spi_device_configure_flash_en4b_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpEnter4bAddr));
  CHECK_DIF_OK(dif_spi_device_configure_flash_ex4b_command(
      spi_device, kDifToggleEnabled, kSpiDeviceFlashOpExit4bAddr));

  if (upload_write_commands) {
    CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpReadStatus1, kDifToggleEnabled));
    CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpReadStatus2, kDifToggleEnabled));
    CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpReadStatus3, kDifToggleEnabled));
    CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpWriteEnable, kDifToggleEnabled));
    CHECK_DIF_OK(dif_spi_device_set_passthrough_command_filter(
        spi_device, kSpiDeviceFlashOpWriteDisable, kDifToggleEnabled));
  }
}
