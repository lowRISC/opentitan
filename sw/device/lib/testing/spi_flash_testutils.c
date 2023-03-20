// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_flash_testutils.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

void spi_flash_testutils_read_id(dif_spi_host_t *spih,
                                 spi_flash_testutils_jedec_id_t *id) {
  CHECK(spih != NULL);
  CHECK(id != NULL);

  uint8_t buffer[32];
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpReadJedec,
      },
      {
          .type = kDifSpiHostSegmentTypeRx,
          .rx =
              {
                  .width = kDifSpiHostWidthStandard,
                  .buf = buffer,
                  .length = sizeof(buffer),
              },
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));

  size_t page = 0;
  while ((page < sizeof(buffer)) && (buffer[page] == 0x7fu)) {
    ++page;
  }
  CHECK(page + 3 <= sizeof(buffer));
  id->continuation_len = page;
  id->manufacturer_id = buffer[page];
  id->device_id = buffer[page + 1];
  id->device_id |= (uint16_t)buffer[page + 2] << 8;
}

void spi_flash_testutils_read_sfdp(dif_spi_host_t *spih, uint32_t address,
                                   uint8_t *buffer, size_t length) {
  CHECK(spih != NULL);
  CHECK(buffer != NULL);

  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpReadSfdp,
      },
      {
          .type = kDifSpiHostSegmentTypeAddress,
          .address =
              {
                  .width = kDifSpiHostWidthStandard,
                  .mode = kDifSpiHostAddrMode3b,
                  .address = address,
              },
      },
      {
          .type = kDifSpiHostSegmentTypeDummy,
          .dummy =
              {
                  .width = kDifSpiHostWidthStandard,
                  .length = 8,
              },
      },
      {
          .type = kDifSpiHostSegmentTypeRx,
          .rx =
              {
                  .width = kDifSpiHostWidthStandard,
                  .buf = buffer,
                  .length = length,
              },
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));
}

status_t spi_flash_testutils_read_status(dif_spi_host_t *spih, uint8_t opcode,
                                         size_t length) {
  CHECK(spih != NULL);
  CHECK(length <= 3);
  uint32_t status;
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = opcode,
      },
      {
          .type = kDifSpiHostSegmentTypeRx,
          .rx =
              {
                  .width = kDifSpiHostWidthStandard,
                  .buf = &status,
                  .length = length,
              },
      },
  };
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));
  return OK_STATUS(status);
}

status_t spi_flash_testutils_write_status(dif_spi_host_t *spih, uint8_t opcode,
                                          uint32_t status, size_t length) {
  CHECK(spih != NULL);
  CHECK(length <= 3);
  spi_flash_testutils_issue_write_enable(spih);
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = opcode,
      },
      {
          .type = kDifSpiHostSegmentTypeTx,
          .tx =
              {
                  .width = kDifSpiHostWidthStandard,
                  .buf = &status,
                  .length = length,
              },
      },
  };
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));
  return OK_STATUS();
}

void spi_flash_testutils_wait_until_not_busy(dif_spi_host_t *spih) {
  CHECK(spih != NULL);
  status_t status;

  do {
    status =
        spi_flash_testutils_read_status(spih, kSpiDeviceFlashOpReadStatus1, 1);
    CHECK_STATUS_OK(status);
  } while (status.value & kSpiFlashStatusBitWip);
}

void spi_flash_testutils_issue_write_enable(dif_spi_host_t *spih) {
  CHECK(spih != NULL);
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpWriteEnable,
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));
}

void spi_flash_testutils_erase_chip(dif_spi_host_t *spih) {
  CHECK(spih != NULL);
  spi_flash_testutils_issue_write_enable(spih);

  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpChipErase,
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));
  spi_flash_testutils_wait_until_not_busy(spih);
}

void spi_flash_testutils_erase_op(dif_spi_host_t *spih, uint8_t opcode,
                                  uint32_t address, bool addr_is_4b) {
  CHECK(spih != NULL);
  spi_flash_testutils_issue_write_enable(spih);

  dif_spi_host_addr_mode_t addr_mode =
      addr_is_4b ? kDifSpiHostAddrMode4b : kDifSpiHostAddrMode3b;
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = opcode,
      },
      {
          .type = kDifSpiHostSegmentTypeAddress,
          .address =
              {
                  .width = kDifSpiHostWidthStandard,
                  .mode = addr_mode,
                  .address = address,
              },
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));

  spi_flash_testutils_wait_until_not_busy(spih);
}

void spi_flash_testutils_erase_sector(dif_spi_host_t *spih, uint32_t address,
                                      bool addr_is_4b) {
  spi_flash_testutils_erase_op(spih, kSpiDeviceFlashOpSectorErase, address,
                               addr_is_4b);
}

void spi_flash_testutils_program_op(dif_spi_host_t *spih, uint8_t opcode,
                                    uint8_t *payload, size_t length,
                                    uint32_t address, bool addr_is_4b) {
  CHECK(spih != NULL);
  CHECK(payload != NULL);
  CHECK(length <= 256);  // Length must be less than a page size.

  spi_flash_testutils_issue_write_enable(spih);

  dif_spi_host_addr_mode_t addr_mode =
      addr_is_4b ? kDifSpiHostAddrMode4b : kDifSpiHostAddrMode3b;
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = opcode,
      },
      {
          .type = kDifSpiHostSegmentTypeAddress,
          .address =
              {
                  .width = kDifSpiHostWidthStandard,
                  .mode = addr_mode,
                  .address = address,
              },
      },
      {
          .type = kDifSpiHostSegmentTypeTx,
          .tx =
              {
                  .width = kDifSpiHostWidthStandard,
                  .buf = payload,
                  .length = length,
              },
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));

  spi_flash_testutils_wait_until_not_busy(spih);
}

void spi_flash_testutils_program_page(dif_spi_host_t *spih, uint8_t *payload,
                                      size_t length, uint32_t address,
                                      bool addr_is_4b) {
  spi_flash_testutils_program_op(spih, kSpiDeviceFlashOpPageProgram, payload,
                                 length, address, addr_is_4b);
}

void spi_flash_testutils_read_op(dif_spi_host_t *spih, uint8_t opcode,
                                 uint8_t *payload, size_t length,
                                 uint32_t address, bool addr_is_4b,
                                 uint8_t width, uint8_t dummy) {
  CHECK(spih != NULL);
  CHECK(payload != NULL);
  CHECK(length <= 256);  // Length must be less than a page size.
  CHECK(width == 1 || width == 2 || width == 4);

  dif_spi_host_addr_mode_t addr_mode =
      addr_is_4b ? kDifSpiHostAddrMode4b : kDifSpiHostAddrMode3b;
  dif_spi_host_width_t data_width = width == 1   ? kDifSpiHostWidthStandard
                                    : width == 2 ? kDifSpiHostWidthDual
                                                 : kDifSpiHostWidthQuad;

  dif_spi_host_segment_t transaction[4] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = opcode,
      },
      {
          .type = kDifSpiHostSegmentTypeAddress,
          .address =
              {
                  .width = kDifSpiHostWidthStandard,
                  .mode = addr_mode,
                  .address = address,
              },
      },
      {
          .type = kDifSpiHostSegmentTypeDummy,
          .dummy =
              {
                  .width = kDifSpiHostWidthStandard,
                  .length = dummy,
              },
      },
      {
          .type = kDifSpiHostSegmentTypeRx,
          .rx =
              {
                  .width = data_width,
                  .buf = payload,
                  .length = length,
              },
      },
  };
  CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                        ARRAYSIZE(transaction)));
}

status_t spi_flash_testutils_quad_enable(dif_spi_host_t *spih, uint8_t method,
                                         bool enabled) {
  uint32_t status;
  switch (method) {
    case 0:
      // Device does not have a QE bit.
      break;
    case 1:
      // QE is bit1 of status reg 2.
      // Set/clear via two-byte reads/writes via SR1 opcodes.
      // Writing only one byte to SR1 clears SR2.
      status = TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 2));
      status = bitfield_bit32_write(status, 9, enabled);
      status = TRY(spi_flash_testutils_write_status(
          spih, kSpiDeviceFlashOpWriteStatus1, status, enabled ? 2 : 1));
      break;
    case 2:
      // QE is bit6 of status reg 1.
      status = TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 1));
      status = bitfield_bit32_write(status, 6, enabled);
      status = TRY(spi_flash_testutils_write_status(
          spih, kSpiDeviceFlashOpWriteStatus1, status, 1));
      break;
    case 3:
      // QE is bit7 of status reg 2.
      // Use "status register 2" opcodes.
      status = TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus2, 1));
      status = bitfield_bit32_write(status, 7, enabled);
      status = TRY(spi_flash_testutils_write_status(
          spih, kSpiDeviceFlashOpWriteStatus2, status, 1));
      break;
    case 4:
      // QE is bit1 of status reg 2.
      // Set/clear via two-byte reads/writes via SR1 opcodes.
      // Writing only one byte to SR1 does not affcet SR2.
      status = TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 2));
      status = bitfield_bit32_write(status, 9, enabled);
      status = TRY(spi_flash_testutils_write_status(
          spih, kSpiDeviceFlashOpWriteStatus1, status, 2));
      break;
    case 5:
      // QE is bit1 of status reg 2.
      // Requires reading status reg via SR1/SR2 opcodes.
      // Set/clear via two-byte reads/writes via SR1 opcodes.
      status = TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 1));
      status |= TRY(spi_flash_testutils_read_status(
                    spih, kSpiDeviceFlashOpReadStatus2, 1))
                << 8;
      status = bitfield_bit32_write(status, 9, enabled);
      status = TRY(spi_flash_testutils_write_status(
          spih, kSpiDeviceFlashOpWriteStatus1, status, 2));
      break;
    case 6:
      // QE is bit1 of status reg 2.
      // Requires reading status reg via SR1/SR2/SR3 opcodes.
      // Set/clear via one-byte writes via SR2 opcode.
      status = TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus2, 1));
      status = bitfield_bit32_write(status, 1, enabled);
      status = TRY(spi_flash_testutils_write_status(
          spih, kSpiDeviceFlashOpWriteStatus2, status, 1));
      break;
    case 7:
      // Reserved.
      return INVALID_ARGUMENT();
      break;
  }
  return OK_STATUS();
}
