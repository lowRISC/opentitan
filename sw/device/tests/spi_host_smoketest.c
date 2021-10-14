// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/test_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

void hexdump(void *addr, size_t len) {
  char buf[17];
  uint8_t *p = (uint8_t *)addr;
  size_t i, j;

  for (i = 0; i < len; i += 16) {
    base_printf("0x%08x ", i);
    for (j = 0; j < 16; ++j, ++p) {
      if (i + j >= len)
        break;
      uint8_t val = *p;
      base_printf(" %02x", val);
      buf[j] = (val >= 32 && val < 127) ? val : '.';
      buf[j + 1] = 0;
    }
    while (j < 16) {
      base_printf("   ");
      ++j;
    }
    base_printf("  %s\r\n", buf);
  }
}

uint8_t buf[256];

void read_sfdp(dif_spi_host_t *spi_host) {
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
  dif_spi_host_transaction_t sfdp = {
      .csid = 0,
      .length = ARRAYSIZE(segments),
      .segments = segments,
  };

  CHECK_DIF_OK(dif_spi_host_start(spi_host, &sfdp));
  hexdump(buf, sizeof(buf));
}

bool test_main(void) {
  dif_spi_host_t spi_host;
  LOG_INFO("spi_host init");
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host));

  LOG_INFO("spi_host configure");
  CHECK(dif_spi_host_configure(&spi_host,
                               (dif_spi_host_config_t){
                                   .spi_clock = 1000000,
                                   .cpol = false,
                               }) == kDifOk,
        "SPI_HOST config failed!");

  LOG_INFO("spi_host read_sfdp");
  read_sfdp(&spi_host);
  LOG_INFO("spi_host done");
  return true;
}
