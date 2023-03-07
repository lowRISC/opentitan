// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/spi_flash_testutils.h"

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

void spi_flash_testutils_wait_until_not_busy(dif_spi_host_t *spih) {
  CHECK(spih != NULL);
  uint8_t status;

  do {
    dif_spi_host_segment_t transaction[] = {
        {
            .type = kDifSpiHostSegmentTypeOpcode,
            .opcode = kSpiDeviceFlashOpReadStatus1,
        },
        {
            .type = kDifSpiHostSegmentTypeRx,
            .rx =
                {
                    .width = kDifSpiHostWidthStandard,
                    .buf = &status,
                    .length = 1,
                },
        },
    };
    CHECK_DIF_OK(dif_spi_host_transaction(spih, /*csid=*/0, transaction,
                                          ARRAYSIZE(transaction)));
  } while (status & kSpiFlashStatusBitWip);
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

void spi_flash_testutils_erase_sector(dif_spi_host_t *spih, uint32_t address,
                                      bool addr_is_4b) {
  CHECK(spih != NULL);
  spi_flash_testutils_issue_write_enable(spih);

  dif_spi_host_addr_mode_t addr_mode =
      addr_is_4b ? kDifSpiHostAddrMode4b : kDifSpiHostAddrMode3b;
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpSectorErase,
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

void spi_flash_testutils_program_page(dif_spi_host_t *spih, uint8_t *payload,
                                      size_t length, uint32_t address,
                                      bool addr_is_4b) {
  CHECK(spih != NULL);
  CHECK(payload != NULL);
  CHECK(length <= 256);  // Length must be less than a page size.

  spi_flash_testutils_issue_write_enable(spih);

  dif_spi_host_addr_mode_t addr_mode =
      addr_is_4b ? kDifSpiHostAddrMode4b : kDifSpiHostAddrMode3b;
  dif_spi_host_segment_t transaction[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = kSpiDeviceFlashOpPageProgram,
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
