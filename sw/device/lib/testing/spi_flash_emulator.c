// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_flash_emulator.h"

#include <stdalign.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"

enum {
  // JEDEC standard continuation code.
  kJedecContCode = 0x7f,
  // JEDEC ID of lowRISC.
  kJedecManufacturer = 0xEF,
  // lowRISC is on page 12 of JEDEC IDs.
  kJedecContCodeCount = 12,
  // A density of 24 corresponds to 16MiB (1<<24 bytes).
  kJedecDensity = 24,
  // The standard SFDP signature value.
  kSfdpSignature = 0x50444653,
};

typedef struct sfdp_header {
  uint32_t signature;
  uint8_t minor;
  uint8_t major;
  uint8_t nph;
  uint8_t reserved;
} sfdp_header_t;

typedef struct parameter_header {
  uint8_t param_id;
  uint8_t minor;
  uint8_t major;
  uint8_t length;
  uint8_t table_pointer[3];
  uint8_t pad;
} parameter_header_t;

typedef struct bfpt {
  uint32_t data[9];
} bfpt_t;

typedef struct sfdp {
  sfdp_header_t header;
  parameter_header_t param;
  bfpt_t bfpt;
} sfdp_t;

static status_t prepare_sfdp(dif_spi_host_t *spih,
                             dif_spi_device_handle_t *spid) {
  alignas(uint32_t) uint8_t data[256];
  spi_flash_testutils_read_sfdp(spih, 0, data, sizeof(data));

  // TODO: present a better SFDP table.  This table is as simple
  // as possible and copies only a few bits of relevant data
  // from the backend EEPROM's table.
  sfdp_t sfdp = {
      .header = {.signature = kSfdpSignature,
                 .minor = 0,
                 .major = 1,
                 .nph = 0,
                 .reserved = 0xFF},
      .param =
          {
              .param_id = 0x00,
              .minor = 0,
              .major = 1,
              .length = sizeof(bfpt_t) / sizeof(uint32_t),
              .table_pointer = {(uint8_t)offsetof(sfdp_t, bfpt)},
              .pad = 0xFF,
          },
      .bfpt = {0},
  };

  uint32_t offset =
      read_32(data + offsetof(sfdp_t, param.table_pointer)) & 0x00FFFFFF;
  if (offset >= sizeof(data)) {
    return INVALID_ARGUMENT();
  }

  // We want to copy SFDP word 0 from the eeprom and preserve the
  // block_erase_size, write_granularity, write_en_required, write_en_opcode,
  // erase_opcode, support_fast_read_112, address_modes and
  // support_fast_read_114 fields.
  sfdp.bfpt.data[0] = read_32(data + offset);
  sfdp.bfpt.data[0] &= 0x0047FFFF;
  // Preserve the entire density field.
  sfdp.bfpt.data[1] = read_32(data + offset + 1 * sizeof(uint32_t));
  // Preserve the 1-1-4 parameters, discard the 1-4-4 parameters.
  sfdp.bfpt.data[2] = read_32(data + offset + 2 * sizeof(uint32_t));
  sfdp.bfpt.data[2] &= 0xFFFF0000;
  // Preserve the sector erase information.
  sfdp.bfpt.data[7] = read_32(data + offset + 7 * sizeof(uint32_t));
  sfdp.bfpt.data[8] = read_32(data + offset + 8 * sizeof(uint32_t));

  TRY(dif_spi_device_write_flash_buffer(spid, kDifSpiDeviceFlashBufferTypeSfdp,
                                        0, sizeof(sfdp), (uint8_t *)&sfdp));
  return OK_STATUS();
}

static status_t prepare_jedec_id(dif_spi_device_handle_t *spid) {
  dif_spi_device_flash_id_t id = {
      // TODO: configure a density that reflects the backend eeprom.
      .device_id = kJedecDensity << 8,
      .manufacturer_id = kJedecManufacturer,
      .continuation_code = kJedecContCode,
      .num_continuation_code = kJedecContCodeCount,
  };
  TRY(dif_spi_device_set_flash_id(spid, id));
  return OK_STATUS();
}

status_t spi_flash_emulator(dif_spi_host_t *spih,
                            dif_spi_device_handle_t *spid) {
  // TODO: add a mode that uses spi_device address translation.
  LOG_INFO("Configuring spi_flash_emulator.");
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleDisabled));
  TRY(prepare_sfdp(spih, spid));
  TRY(prepare_jedec_id(spid));
  TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleEnabled));
  LOG_INFO("Starting spi_flash_emulator.");

  bool running = true;
  while (running) {
    upload_info_t info = {0};
    TRY(spi_device_testutils_wait_for_upload(spid, &info));

    TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleDisabled));
    switch (info.opcode) {
      // TODO: process the alternate erase opcodes from the BFPT.
      case kSpiDeviceFlashOpChipErase:
        spi_flash_testutils_erase_chip(spih);
        break;
      case kSpiDeviceFlashOpSectorErase:
        spi_flash_testutils_erase_sector(spih, info.address, info.addr_4b);
        break;
      case kSpiDeviceFlashOpPageProgram:
        spi_flash_testutils_program_page(spih, info.data, info.data_len,
                                         info.address, info.addr_4b);
        break;
      case kSpiDeviceFlashOpReset:
        running = false;
        break;
      default:
        LOG_ERROR("Unknown SPI op: %02x", info.opcode);
    }
    TRY(dif_spi_device_set_passthrough_mode(spid, kDifToggleEnabled));
    TRY(dif_spi_device_set_flash_status_registers(spid, 0));
  }
  LOG_INFO("Exiting spi_flash_emulator.");
  return OK_STATUS();
}
