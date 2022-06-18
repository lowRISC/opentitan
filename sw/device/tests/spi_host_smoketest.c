// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

#define SFDP_SIGNATURE 0x50444653

OTTF_DEFINE_TEST_CONFIG();

void read_sfdp(dif_spi_host_t *spi_host) {
  uint8_t buf[256];
  dif_spi_host_segment_t segments[] = {
      {
          .type = kDifSpiHostSegmentTypeOpcode,
          .opcode = 0x5a,
      },
      {
          .type = kDifSpiHostSegmentTypeAddress,
          .address =
              {
                  .width = kDifSpiHostWidthStandard,
                  .mode = kDifSpiHostAddrMode3b,
                  .address = 0x0,
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
                  .buf = buf,
                  .length = sizeof(buf),
              },
      },
  };
  CHECK_DIF_OK(
      dif_spi_host_transaction(spi_host, 0, segments, ARRAYSIZE(segments)));

  uint32_t sfdp = read_32(buf);
  LOG_INFO("SFDP signature is 0x%08x", sfdp);
  CHECK(sfdp == SFDP_SIGNATURE, "Expected to find the SFDP signature!");
}

bool test_main(void) {
  dif_spi_host_t spi_host;
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host));

  CHECK_DIF_OK(dif_spi_host_configure(
                   &spi_host,
                   (dif_spi_host_config_t){
                       .spi_clock = 1000000,
                       .peripheral_clock_freq_hz = kClockFreqPeripheralHz,
                   }),
               "SPI_HOST config failed!");
  CHECK_DIF_OK(dif_spi_host_output_set_enabled(&spi_host, true));

  read_sfdp(&spi_host);
  return true;
}
