// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/spi_host_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/tests/spi_host_flash_test_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

static void init_test(dif_spi_host_t *spi_host) {
  dif_pinmux_t pinmux;
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux));
  CHECK_STATUS_OK(
      spi_host1_pinmux_connect_to_bob(&pinmux, kTopEarlgreyPinmuxMioOutIoc11));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, spi_host));

  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");

  CHECK_DIF_OK(dif_spi_host_configure(spi_host,
                                      (dif_spi_host_config_t){
                                          .spi_clock = 1000000,
                                          .peripheral_clock_freq_hz =
                                              (uint32_t)kClockFreqPeripheralHz,
                                      }),
               "SPI_HOST config failed!");

  CHECK_DIF_OK(dif_spi_host_output_set_enabled(spi_host, true));
}

bool test_main(void) {
  dif_spi_host_t spi_host;

  init_test(&spi_host);
  enum GigadeviceVendorSpecific {
    kDeviceId = 0x1940,
    kManufactureId = 0xC8,
    kPageQuadProgramOpcode = 0x32,
  };

  status_t result = OK_STATUS();
  EXECUTE_TEST(result, test_software_reset, &spi_host);
  EXECUTE_TEST(result, test_read_sfdp, &spi_host);
  EXECUTE_TEST(result, test_sector_erase, &spi_host);
  EXECUTE_TEST(result, test_read_jedec, &spi_host, kDeviceId, kManufactureId);
  EXECUTE_TEST(result, test_enable_quad_mode, &spi_host);
  EXECUTE_TEST(result, test_page_program, &spi_host);
  if (is_4_bytes_address_mode_supported()) {
    EXECUTE_TEST(result, test_4bytes_address, &spi_host);
  }
  EXECUTE_TEST(result, test_fast_read, &spi_host);
  EXECUTE_TEST(result, test_dual_read, &spi_host);
  EXECUTE_TEST(result, test_quad_read, &spi_host);

  // The Gigadevice flash `4PP` opcode operates in 1-1-4 mode.
  EXECUTE_TEST(result, test_page_program_quad, &spi_host,
               kPageQuadProgramOpcode, kTransactionWidthMode114);
  EXECUTE_TEST(result, test_erase_32k_block, &spi_host);
  EXECUTE_TEST(result, test_erase_64k_block, &spi_host);

  return status_ok(result);
}
