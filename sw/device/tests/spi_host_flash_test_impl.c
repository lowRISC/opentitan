// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// A data pattern to program into the chip:
// From: http://www.abrahamlincolnonline.org/lincoln/speeches/gettysburg.htm
static const char kGettysburgPrelude[256] =
    "Four score and seven years ago our fathers brought forth on this "
    "continent, a new nation, conceived in Liberty, and dedicated to the "
    "proposition that all men are created equal.";

// The SFDP structure we'll read out of the chip.
typedef struct sfdp {
  union {
    struct {
      spi_flash_testutils_sfdp_header_t header;
      spi_flash_testutils_parameter_header_t param;
    };
    uint8_t data[256];
  };
  uint32_t *bfpt;
} sfdp_t;

sfdp_t sfdp;

status_t test_software_reset(dif_spi_host_t *spi) {
  // The software reset sequence is two transactions: RSTEN followed by RST.
  dif_spi_host_segment_t op = {
      .type = kDifSpiHostSegmentTypeOpcode,
      .opcode = {.opcode = kSpiDeviceFlashOpResetEnable,
                 .width = kDifSpiHostWidthStandard}};
  TRY(dif_spi_host_transaction(spi, /*cs_id=*/0, &op, 1));

  TRY(dif_spi_host_transaction(spi, /*cs_id=*/0, &op, 1));
  return OK_STATUS();
}

status_t test_read_sfdp(dif_spi_host_t *spi) {
  TRY(spi_flash_testutils_read_sfdp(spi, 0, sfdp.data, sizeof(sfdp.data)));
  LOG_INFO("SFDP signature is 0x%08x", sfdp.header.signature);
  CHECK(sfdp.header.signature == kSfdpSignature,
        "Expected to find the SFDP signature!");

  uint32_t bfpt_offset = (uint32_t)sfdp.param.table_pointer[0] |
                         (uint32_t)(sfdp.param.table_pointer[1] << 8) |
                         (uint32_t)(sfdp.param.table_pointer[2] << 16);
  sfdp.bfpt = (uint32_t *)(sfdp.data + bfpt_offset);
  return OK_STATUS();
}

status_t test_read_jedec(dif_spi_host_t *spi, uint16_t device_id,
                         uint8_t manufacture_id) {
  spi_flash_testutils_jedec_id_t jdec;
  TRY(spi_flash_testutils_read_id(spi, &jdec));
  TRY_CHECK(jdec.device_id == device_id, "Expected %x, got %x!", device_id,
            jdec.device_id);
  TRY_CHECK(jdec.manufacturer_id == manufacture_id, "Expected %x, got %x!",
            manufacture_id, jdec.manufacturer_id);
  return OK_STATUS();
}

status_t test_sector_erase(dif_spi_host_t *spi) {
  TRY(spi_flash_testutils_erase_sector(spi, 0, false));

  // Check that the first page of flash actually got erased.
  uint8_t buf[256] = {0};
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadNormal, buf,
                                  sizeof(buf),
                                  /*address=*/0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/1,
                                  /*dummy=*/0));
  uint8_t expected[256];
  memset(expected, 0xFF, sizeof(expected));
  TRY_CHECK_ARRAYS_EQ(buf, expected, ARRAYSIZE(expected));
  return OK_STATUS();
}

status_t test_enable_quad_mode(dif_spi_host_t *spi) {
  if (sfdp.param.length < 14) {
    return INVALID_ARGUMENT();
  }
  uint8_t mech =
      (uint8_t)bitfield_field32_read(sfdp.bfpt[14], SPI_FLASH_QUAD_ENABLE);
  LOG_INFO("Setting the EEPROM's QE bit via mechanism %d", mech);
  TRY(spi_flash_testutils_quad_enable(spi, mech, /*enabled=*/true));
  return OK_STATUS();
}

// Program a pattern into the flash part and read it back.
status_t test_page_program(dif_spi_host_t *spi) {
  TRY(spi_flash_testutils_program_page(spi, kGettysburgPrelude,
                                       sizeof(kGettysburgPrelude),
                                       /*address=*/0, /*addr_is_4b=*/0));

  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadNormal, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/1,
                                  /*dummy=*/0));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

status_t test_page_program_quad(
    dif_spi_host_t *spi, uint8_t opcode,
    spi_flash_testutils_transaction_width_mode_t page_program_mode) {
  enum { kPageSize = 256, kAddress = kPageSize * 10 };

  TRY(spi_flash_testutils_erase_sector(spi, kAddress, false));

  TRY(spi_flash_testutils_program_op(
      spi, opcode, kGettysburgPrelude, sizeof(kGettysburgPrelude),
      /*address=*/kAddress, /*addr_is_4b=*/false, page_program_mode));

  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadNormal, buf,
                                  sizeof(buf), kAddress,
                                  /*addr_is_4b=*/false,
                                  /*width=*/1,
                                  /*dummy=*/0));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

// Read the flash device using the "fast read" opcode.
status_t test_fast_read(dif_spi_host_t *spi) {
  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadFast, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/1,
                                  /*dummy=*/8));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

// Read the flash device using the "fast dual read" opcode.
status_t test_dual_read(dif_spi_host_t *spi) {
  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadDual, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/2,
                                  /*dummy=*/8));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

// Read the flash device using the "fast quad read" opcode.
status_t test_quad_read(dif_spi_host_t *spi) {
  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadQuad, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/4,
                                  /*dummy=*/8));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

bool is_4_bytes_address_mode_supported(void) {
  enum { kSupportOnly3Bytes, kSupport3and4Bytes, kSupportOnly4Bytes };
  uint32_t address_mode =
      bitfield_field32_read(sfdp.bfpt[0], SPI_FLASH_ADDRESS_MODE);
  return (address_mode == kSupport3and4Bytes ||
          address_mode == kSupportOnly4Bytes);
}

status_t test_4bytes_address(dif_spi_host_t *spi) {
  enum { kAddress = 0x01000100, kSectorSize = 4096 };
  static_assert(kAddress % kSectorSize,
                "Should be at the beginning of the sector.");

  TRY(spi_flash_testutils_enter_4byte_address_mode(spi));
  TRY(spi_flash_testutils_erase_sector(spi, kAddress, true));

  TRY(spi_flash_testutils_program_page(spi, kGettysburgPrelude,
                                       sizeof(kGettysburgPrelude), kAddress,
                                       /*addr_is_4b=*/true));

  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadNormal, buf,
                                  sizeof(buf), kAddress,
                                  /*addr_is_4b=*/true,
                                  /*width=*/1,
                                  /*dummy=*/0));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return spi_flash_testutils_exit_4byte_address_mode(spi);
}

status_t test_erase_32k_block(dif_spi_host_t *spi) {
  enum { kPageSize = 256, kBlockSize = 32 * 1024, kAddress = kBlockSize * 3 };
  TRY(spi_flash_testutils_erase_block32k(spi, kAddress, false));

  uint8_t expected[256];
  memset(expected, 0xFF, sizeof(expected));
  uint8_t dummy[256];
  memset(dummy, 0x5A, sizeof(dummy));

  for (size_t addr = kAddress; addr < kAddress + kBlockSize;
       addr += kPageSize) {
    uint8_t buf[256] = {0};
    // Check that all the pages in the block actually got erased.
    TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadNormal, buf,
                                    sizeof(buf),
                                    /*address=*/addr,
                                    /*addr_is_4b=*/false,
                                    /*width=*/1,
                                    /*dummy=*/0));
    TRY_CHECK_ARRAYS_EQ(buf, expected, ARRAYSIZE(expected));

    // Write dummy data to make sure that the next time the block will really be
    // erased.
    TRY(spi_flash_testutils_program_page(spi, dummy, sizeof(dummy),
                                         /*address=*/addr,
                                         /*addr_is_4b=*/false));
  }

  return OK_STATUS();
}

status_t test_erase_64k_block(dif_spi_host_t *spi) {
  enum { kPageSize = 256, kBlockSize = 64 * 1024, kAddress = kBlockSize * 5 };
  TRY(spi_flash_testutils_erase_block64k(spi, kAddress, false));

  uint8_t expected[256];
  memset(expected, 0xFF, sizeof(expected));
  uint8_t dummy[256];
  memset(dummy, 0x5A, sizeof(dummy));

  for (size_t addr = kAddress; addr < kAddress + kBlockSize;
       addr += kPageSize) {
    uint8_t buf[256] = {0};
    // Check that all the pages in the block actually got erased.
    TRY(spi_flash_testutils_read_op(spi, kSpiDeviceFlashOpReadNormal, buf,
                                    sizeof(buf),
                                    /*address=*/addr,
                                    /*addr_is_4b=*/false,
                                    /*width=*/1,
                                    /*dummy=*/0));
    TRY_CHECK_ARRAYS_EQ(buf, expected, ARRAYSIZE(expected));

    // Write dummy data to make sure that the next time the block will really be
    // erased.
    TRY(spi_flash_testutils_program_page(spi, dummy, sizeof(dummy),
                                         /*address=*/addr,
                                         /*addr_is_4b=*/false));
  }

  return OK_STATUS();
}
