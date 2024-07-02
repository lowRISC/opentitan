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
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_utils.h"
#include "sw/device/tests/spi_host_flash_test_impl.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

enum {
  kDefaultTimeoutMicros = 50000,
};

uint8_t backdoor_cpha = UINT8_MAX;
uint8_t backdoor_cpol = UINT8_MAX;
uint32_t backdoor_data = UINT32_MAX;

static status_t spi_config_test(dif_spi_host_t *spi);

static status_t configure_pinmux(const dif_pinmux_t *pinmux);

bool test_main(void) {
  dif_spi_host_t spi_host;
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);

  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host));

  configure_pinmux(&pinmux);
  for (size_t i = 0; i < 4; ++i) {
    CHECK_STATUS_OK(spi_config_test(&spi_host));
  }
  return true;
}

static status_t spi_config_test(dif_spi_host_t *spi) {
  dif_spi_host_config_t config = {
      .spi_clock = 40000,
      .peripheral_clock_freq_hz = (uint32_t)kClockFreqUsbHz,
  };
  backdoor_cpha = UINT8_MAX;
  backdoor_cpol = UINT8_MAX;
  backdoor_data = UINT32_MAX;

  OTTF_WAIT_FOR(backdoor_cpha != UINT8_MAX, kDefaultTimeoutMicros);
  config.cpha = backdoor_cpha;
  OTTF_WAIT_FOR(backdoor_cpol != UINT8_MAX, kDefaultTimeoutMicros);
  config.cpol = backdoor_cpol;
  TRY(dif_spi_host_output_set_enabled(spi, false));
  TRY(dif_spi_host_configure(spi, config));
  TRY(dif_spi_host_output_set_enabled(spi, true));
  LOG_INFO("Mode : CPOL=%d,CPHA=%d", config.cpol, config.cpha);

  static uint32_t address = 0;
  OTTF_WAIT_FOR(backdoor_data != UINT32_MAX, kDefaultTimeoutMicros);
  uint8_t data[sizeof(backdoor_data)];
  memcpy(data, &backdoor_data, sizeof(data));
  busy_spin_micros(70000);
  TRY(spi_flash_testutils_program_page(spi, data, sizeof(data), address,
                                       false));
  return OK_STATUS();
}

static status_t configure_pinmux(const dif_pinmux_t *pinmux) {
  // CSB.
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor10,
                               kTopEarlgreyPinmuxOutselSpiHost1Csb));
  // SCLK.
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor11,
                               kTopEarlgreyPinmuxOutselSpiHost1Sck));
  // SD0.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0,
                              kTopEarlgreyPinmuxInselIor12));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor12,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd0));

  // SD1.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1,
                              kTopEarlgreyPinmuxInselIor13));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIor13,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd1));
  return OK_STATUS();
}
