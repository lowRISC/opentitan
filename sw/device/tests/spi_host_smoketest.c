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
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

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

dif_spi_host_t spi_host;
sfdp_t sfdp;

status_t test_software_reset(void) {
  // The software reset sequence is two transactions: RSTEN followed by RST.
  dif_spi_host_segment_t op = {
      .type = kDifSpiHostSegmentTypeOpcode,
      .opcode = kSpiDeviceFlashOpResetEnable,
  };
  TRY(dif_spi_host_transaction(&spi_host, /*cs_id=*/0, &op, 1));

  op.opcode = kSpiDeviceFlashOpResetEnable;
  TRY(dif_spi_host_transaction(&spi_host, /*cs_id=*/0, &op, 1));
  return OK_STATUS();
}

status_t test_read_sfdp(void) {
  TRY(spi_flash_testutils_read_sfdp(&spi_host, 0, sfdp.data,
                                    sizeof(sfdp.data)));
  LOG_INFO("SFDP signature is 0x%08x", sfdp.header.signature);
  CHECK(sfdp.header.signature == kSfdpSignature,
        "Expected to find the SFDP signature!");

  uint32_t bfpt_offset = (uint32_t)sfdp.param.table_pointer[0] |
                         (uint32_t)(sfdp.param.table_pointer[1] << 8) |
                         (uint32_t)(sfdp.param.table_pointer[2] << 16);
  sfdp.bfpt = (uint32_t *)(sfdp.data + bfpt_offset);
  return OK_STATUS();
}

status_t test_erase(void) {
  TRY(spi_flash_testutils_erase_sector(&spi_host, 0, false));

  // Check that the first page of flash actually got erased.
  uint8_t buf[256] = {0};
  TRY(spi_flash_testutils_read_op(&spi_host, kSpiDeviceFlashOpReadNormal, buf,
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

status_t test_enable_quad_mode(void) {
  if (sfdp.param.length < 14) {
    return INVALID_ARGUMENT();
  }
  uint8_t mech =
      (uint8_t)bitfield_field32_read(sfdp.bfpt[14], SPI_FLASH_QUAD_ENABLE);
  LOG_INFO("Setting the EEPROM's QE bit via mechanism %d", mech);
  TRY(spi_flash_testutils_quad_enable(&spi_host, mech, /*enabled=*/true));
  return OK_STATUS();
}

// Program a pattern into the flash part and read it back.
status_t test_page_program(void) {
  TRY(spi_flash_testutils_program_page(&spi_host, kGettysburgPrelude,
                                       sizeof(kGettysburgPrelude),
                                       /*address=*/0, /*addr_is_4b=*/0));

  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(&spi_host, kSpiDeviceFlashOpReadNormal, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/1,
                                  /*dummy=*/0));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

// Read the flash device using the "fast read" opcode.
status_t test_fast_read(void) {
  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(&spi_host, kSpiDeviceFlashOpReadFast, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/1,
                                  /*dummy=*/8));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

// Read the flash device using the "fast dual read" opcode.
status_t test_dual_read(void) {
  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(&spi_host, kSpiDeviceFlashOpReadDual, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/2,
                                  /*dummy=*/8));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

// Read the flash device using the "fast quad read" opcode.
status_t test_quad_read(void) {
  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(&spi_host, kSpiDeviceFlashOpReadQuad, buf,
                                  sizeof(buf), 0,
                                  /*addr_is_4b=*/false,
                                  /*width=*/4,
                                  /*dummy=*/8));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return OK_STATUS();
}

static bool is_4_bytes_address_mode_supported(void) {
  enum { kSupportOnly3Bytes, kSupport3and4Bytes, kSupportOnly4Bytes };
  uint8_t address_mode =
      bitfield_field32_read(sfdp.bfpt[0], SPI_FLASH_ADDRESS_MODE);
  return (address_mode == kSupport3and4Bytes ||
          address_mode == kSupportOnly4Bytes);
}

status_t test_4bytes_address(void) {
  enum { kAddress = 0x01000100, kSectorSize = 4096 };
  static_assert(kAddress % kSectorSize,
                "Should be at the beginning of the sector.");

  TRY(spi_flash_testutils_enter_4byte_address_mode(&spi_host));
  TRY(spi_flash_testutils_erase_sector(&spi_host, kAddress, true));

  TRY(spi_flash_testutils_program_page(&spi_host, kGettysburgPrelude,
                                       sizeof(kGettysburgPrelude), kAddress,
                                       /*addr_is_4b=*/true));

  uint8_t buf[256];
  TRY(spi_flash_testutils_read_op(&spi_host, kSpiDeviceFlashOpReadNormal, buf,
                                  sizeof(buf), kAddress,
                                  /*addr_is_4b=*/true,
                                  /*width=*/1,
                                  /*dummy=*/0));
  TRY_CHECK_ARRAYS_EQ(buf, kGettysburgPrelude, ARRAYSIZE(kGettysburgPrelude));
  return spi_flash_testutils_exit_4byte_address_mode(&spi_host);
}

bool test_main(void) {
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host));

  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");

  CHECK_DIF_OK(dif_spi_host_configure(&spi_host,
                                      (dif_spi_host_config_t){
                                          .spi_clock = 1000000,
                                          .peripheral_clock_freq_hz =
                                              (uint32_t)kClockFreqPeripheralHz,
                                      }),
               "SPI_HOST config failed!");
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(&spi_host, true));

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, test_software_reset);
  EXECUTE_TEST(result, test_read_sfdp);
  EXECUTE_TEST(result, test_erase);
  EXECUTE_TEST(result, test_enable_quad_mode);
  EXECUTE_TEST(result, test_page_program);
  if (is_4_bytes_address_mode_supported()) {
    EXECUTE_TEST(result, test_4bytes_address);
  }
  EXECUTE_TEST(result, test_fast_read);
  EXECUTE_TEST(result, test_dual_read);
  EXECUTE_TEST(result, test_quad_read);
  return status_ok(result);
}
