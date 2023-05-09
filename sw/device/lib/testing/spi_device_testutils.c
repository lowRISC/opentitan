// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_device_testutils.h"

#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t spi_device_testutils_configure_passthrough(
    dif_spi_device_handle_t *spi_device, uint32_t filters,
    bool upload_write_commands) {
  dif_spi_device_config_t spi_device_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModePassthrough,
  };
  TRY(dif_spi_device_configure(spi_device, spi_device_config));

  // Zero-init the payload memory to avoid X-triggered assertions in sim.
  uint8_t zeroes[256];
  memset(zeroes, 0, sizeof(zeroes));
  TRY(dif_spi_device_write_flash_buffer(spi_device,
                                        kDifSpiDeviceFlashBufferTypePayload, 0,
                                        sizeof(zeroes), zeroes));

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
  static_assert(ARRAYSIZE(read_commands) <= UINT8_MAX,
                "Length of read_commands must fit in uint8_t or we must change "
                "the type of i.");
  for (uint8_t i = 0; i < ARRAYSIZE(read_commands); ++i) {
    uint8_t slot = i + kSpiDeviceReadCommandSlotBase;
    if (bitfield_bit32_read(filters, slot)) {
      TRY(dif_spi_device_set_passthrough_command_filter(
          spi_device, read_commands[i].opcode, kDifToggleEnabled));
    }
    TRY(dif_spi_device_set_flash_command_slot(
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
          // Slot 16: BlockErase32k
          .opcode = kSpiDeviceFlashOpBlockErase32k,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 17: BlockErase64k
          .opcode = kSpiDeviceFlashOpBlockErase64k,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 18: PageProgram
          .opcode = kSpiDeviceFlashOpPageProgram,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 19: SectorErase4b
          .opcode = kSpiDeviceFlashOpSectorErase4b,
          .address_type = kDifSpiDeviceFlashAddr4Byte,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 20: BlockErase32k4b
          .opcode = kSpiDeviceFlashOpBlockErase32k4b,
          .address_type = kDifSpiDeviceFlashAddr4Byte,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 21: BlockErase64k4b
          .opcode = kSpiDeviceFlashOpBlockErase64k4b,
          .address_type = kDifSpiDeviceFlashAddr4Byte,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 22: PageProgram4b
          .opcode = kSpiDeviceFlashOpPageProgram4b,
          .address_type = kDifSpiDeviceFlashAddr4Byte,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },
      {
          // Slot 23: Reset
          .opcode = kSpiDeviceFlashOpReset,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .payload_io_type = kDifSpiDevicePayloadIoNone,
          .upload = upload_write_commands,
          .set_busy_status = upload_write_commands,
      },

  };
  static_assert(ARRAYSIZE(write_commands) <= UINT8_MAX,
                "Length of write_commands must fit into uint8_t");
  for (uint8_t i = 0; i < ARRAYSIZE(write_commands); ++i) {
    uint8_t slot = i + (uint8_t)kSpiDeviceWriteCommandSlotBase;
    if (bitfield_bit32_read(filters, slot) || upload_write_commands) {
      TRY(dif_spi_device_set_passthrough_command_filter(
          spi_device, write_commands[i].opcode, kDifToggleEnabled));
    }
    TRY(dif_spi_device_set_flash_command_slot(
        spi_device, slot, kDifToggleEnabled, write_commands[i]));
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
    TRY(dif_spi_device_read_flash_buffer(spid,
                                         kDifSpiDeviceFlashBufferTypePayload,
                                         start, info->data_len, info->data));
  }

  // Finished: ack the IRQ.
  TRY(dif_spi_device_irq_acknowledge(&spid->dev,
                                     kDifSpiDeviceIrqUploadCmdfifoNotEmpty));
  return OK_STATUS();
}
