// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_flash_testutils.h"

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

status_t spi_flash_testutils_read_id(dif_spi_host_t *spih,
                                     spi_flash_testutils_jedec_id_t *id) {
  TRY_CHECK(spih != NULL);
  TRY_CHECK(id != NULL);

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
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));

  size_t page = 0;
  while ((page < sizeof(buffer)) && (buffer[page] == 0x7fu)) {
    ++page;
  }
  TRY_CHECK(page + 3 <= sizeof(buffer));
  TRY_CHECK(page <= UINT8_MAX);
  id->continuation_len = (uint8_t)page;
  id->manufacturer_id = buffer[page];
  id->device_id = buffer[page + 1];
  id->device_id |= (uint16_t)buffer[page + 2] << 8;
  return OK_STATUS();
}

status_t spi_flash_testutils_read_sfdp(dif_spi_host_t *spih, uint32_t address,
                                       void *buffer, size_t length) {
  TRY_CHECK(spih != NULL);
  TRY_CHECK(buffer != NULL);

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
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));
  return OK_STATUS();
}

status_t spi_flash_testutils_read_status(dif_spi_host_t *spih, uint8_t opcode,
                                         size_t length) {
  TRY_CHECK(spih != NULL);
  TRY_CHECK(length <= 3);
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
  return OK_STATUS((int32_t)status);
}

status_t spi_flash_testutils_write_status(dif_spi_host_t *spih, uint8_t opcode,
                                          uint32_t status, size_t length) {
  TRY_CHECK(spih != NULL);
  TRY_CHECK(length <= 3);
  TRY(spi_flash_testutils_issue_write_enable(spih));
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

status_t spi_flash_testutils_wait_until_not_busy(dif_spi_host_t *spih) {
  TRY_CHECK(spih != NULL);
  int32_t status;

  do {
    status = TRY(
        spi_flash_testutils_read_status(spih, kSpiDeviceFlashOpReadStatus1, 1));
  } while (status & kSpiFlashStatusBitWip);
  return OK_STATUS();
}

status_t spi_flash_testutils_issue_write_enable(dif_spi_host_t *spih) {
  TRY_CHECK(spih != NULL);
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpWriteEnable,
      },
  };
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));
  return OK_STATUS();
}

status_t spi_flash_testutils_erase_chip(dif_spi_host_t *spih) {
  TRY_CHECK(spih != NULL);
  TRY(spi_flash_testutils_issue_write_enable(spih));

  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpChipErase,
      },
  };
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));
  return spi_flash_testutils_wait_until_not_busy(spih);
}

status_t spi_flash_testutils_erase_op(dif_spi_host_t *spih, uint8_t opcode,
                                      uint32_t address, bool addr_is_4b) {
  TRY_CHECK(spih != NULL);
  TRY(spi_flash_testutils_issue_write_enable(spih));

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
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));

  return spi_flash_testutils_wait_until_not_busy(spih);
}

status_t spi_flash_testutils_erase_sector(dif_spi_host_t *spih,
                                          uint32_t address, bool addr_is_4b) {
  return spi_flash_testutils_erase_op(spih, kSpiDeviceFlashOpSectorErase,
                                      address, addr_is_4b);
}

status_t spi_flash_testutils_program_op(dif_spi_host_t *spih, uint8_t opcode,
                                        const void *payload, size_t length,
                                        uint32_t address, bool addr_is_4b) {
  TRY_CHECK(spih != NULL);
  TRY_CHECK(payload != NULL);
  TRY_CHECK(length <= 256);  // Length must be less than a page size.

  TRY(spi_flash_testutils_issue_write_enable(spih));

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
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));

  return spi_flash_testutils_wait_until_not_busy(spih);
}

status_t spi_flash_testutils_program_page(dif_spi_host_t *spih,
                                          const void *payload, size_t length,
                                          uint32_t address, bool addr_is_4b) {
  return spi_flash_testutils_program_op(spih, kSpiDeviceFlashOpPageProgram,
                                        payload, length, address, addr_is_4b);
}

status_t spi_flash_testutils_read_op(dif_spi_host_t *spih, uint8_t opcode,
                                     void *payload, size_t length,
                                     uint32_t address, bool addr_is_4b,
                                     uint8_t width, uint8_t dummy) {
  TRY_CHECK(spih != NULL);
  TRY_CHECK(payload != NULL);
  TRY_CHECK(length <= 256);  // Length must be less than a page size.
  TRY_CHECK(width == 1 || width == 2 || width == 4);

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
  TRY(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                               ARRAYSIZE(transaction)));
  return OK_STATUS();
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
      status = (uint32_t)TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 2));
      status = bitfield_bit32_write(status, 9, enabled);
      TRY(spi_flash_testutils_write_status(spih, kSpiDeviceFlashOpWriteStatus1,
                                           status, enabled ? 2 : 1));
      break;
    case 2:
      // QE is bit6 of status reg 1.
      status = (uint32_t)TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 1));
      status = bitfield_bit32_write(status, 6, enabled);
      TRY(spi_flash_testutils_write_status(spih, kSpiDeviceFlashOpWriteStatus1,
                                           status, 1));
      break;
    case 3:
      // QE is bit7 of status reg 2.
      // Use "status register 2" opcodes.
      status = (uint32_t)TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus2, 1));
      status = bitfield_bit32_write(status, 7, enabled);
      TRY(spi_flash_testutils_write_status(spih, kSpiDeviceFlashOpWriteStatus2,
                                           status, 1));
      break;
    case 4:
      // QE is bit1 of status reg 2.
      // Set/clear via two-byte reads/writes via SR1 opcodes.
      // Writing only one byte to SR1 does not affcet SR2.
      status = (uint32_t)TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 2));
      status = bitfield_bit32_write(status, 9, enabled);
      TRY(spi_flash_testutils_write_status(spih, kSpiDeviceFlashOpWriteStatus1,
                                           status, 2));
      break;
    case 5:
      // QE is bit1 of status reg 2.
      // Requires reading status reg via SR1/SR2 opcodes.
      // Set/clear via two-byte reads/writes via SR1 opcodes.
      status = (uint32_t)TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus1, 1));
      status |= (uint32_t)(TRY(spi_flash_testutils_read_status(
                               spih, kSpiDeviceFlashOpReadStatus2, 1))
                           << 8);
      status = bitfield_bit32_write(status, 9, enabled);
      TRY(spi_flash_testutils_write_status(spih, kSpiDeviceFlashOpWriteStatus1,
                                           status, 2));
      break;
    case 6:
      // QE is bit1 of status reg 2.
      // Requires reading status reg via SR1/SR2/SR3 opcodes.
      // Set/clear via one-byte writes via SR2 opcode.
      status = (uint32_t)TRY(spi_flash_testutils_read_status(
          spih, kSpiDeviceFlashOpReadStatus2, 1));
      status = bitfield_bit32_write(status, 1, enabled);
      TRY(spi_flash_testutils_write_status(spih, kSpiDeviceFlashOpWriteStatus2,
                                           status, 1));
      break;
    case 7:
      // Reserved.
      return INVALID_ARGUMENT();
      break;
  }
  return OK_STATUS();
}

status_t spi_flash_testutils_enter_4byte_address_mode(dif_spi_host_t *spih) {
  dif_spi_host_segment_t op = {
      .type = kDifSpiHostSegmentTypeOpcode,
      .opcode = kSpiDeviceFlashOpEnter4bAddr,
  };
  TRY(dif_spi_host_transaction(spih, /*cs_id=*/0, &op, 1));
  return OK_STATUS();
}

status_t spi_flash_testutils_exit_4byte_address_mode(dif_spi_host_t *spih) {
  dif_spi_host_segment_t op = {
      .type = kDifSpiHostSegmentTypeOpcode,
      .opcode = kSpiDeviceFlashOpExit4bAddr,
  };
  TRY(dif_spi_host_transaction(spih, /*cs_id=*/0, &op, 1));
  return OK_STATUS();
}
