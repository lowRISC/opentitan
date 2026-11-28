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
  // This test uses the hyperdebug bit banging. To ensure accurate signal
  // capture and avoid aliasing, we run the spi at 40kHz, adhering to the
  // Nyquist limit with the Hyperdebug's 100kHz sampling rate.
  kSpiClock = 20000,
};

OTTF_BACKDOOR_VAR
uint8_t backdoor_cpha = UINT8_MAX;
OTTF_BACKDOOR_VAR
uint8_t backdoor_cpol = UINT8_MAX;
OTTF_BACKDOOR_VAR
uint32_t backdoor_data = UINT32_MAX;

static status_t spi_config_test(dif_spi_host_t *spi);

static status_t configure_pinmux(const dif_pinmux_t *pinmux);
static status_t release_pinmux(const dif_pinmux_t *pinmux);

bool test_main(void) {
  dif_spi_host_t spi_host;
  mmio_region_t base_addr =
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR);

  dif_pinmux_t pinmux;
  CHECK_DIF_OK(dif_pinmux_init(base_addr, &pinmux));
  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_host_init(base_addr, &spi_host));

  configure_pinmux(&pinmux);
  for (size_t i = 0; i < 4; ++i) {
    CHECK_STATUS_OK(spi_config_test(&spi_host));
  }
  CHECK_STATUS_OK(release_pinmux(&pinmux));
  return true;
}

static status_t spi_config_test(dif_spi_host_t *spi) {
  dif_spi_host_config_t config = {
      .spi_clock = kSpiClock,
      .peripheral_clock_freq_hz = (uint32_t)kClockFreqHiSpeedPeripheralHz,
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
  memcpy(data, (const void *)&backdoor_data, sizeof(data));
  busy_spin_micros(40000);
  TRY(spi_flash_testutils_program_page(spi, data, sizeof(data), address,
                                       false));
  return OK_STATUS();
}

static status_t configure_pinmux(const dif_pinmux_t *pinmux) {
  // spi_host1 can only reach the IOB pads: CSB on IOB0, SCLK on IOB3, SD0 on
  // IOB1 and SD1 on IOB2.
  // CSB.
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIob0,
                               kTopEarlgreyPinmuxOutselSpiHost1Csb0));
  // SCLK.
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIob3,
                               kTopEarlgreyPinmuxOutselSpiHost1Sck));
  // SD0.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd0,
                              kTopEarlgreyPinmuxInselIob1));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIob1,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd0));

  // SD1.
  TRY(dif_pinmux_input_select(pinmux, kTopEarlgreyPinmuxPeripheralInSpiHost1Sd1,
                              kTopEarlgreyPinmuxInselIob2));
  TRY(dif_pinmux_output_select(pinmux, kTopEarlgreyPinmuxMioOutIob2,
                               kTopEarlgreyPinmuxOutselSpiHost1Sd1));
  return OK_STATUS();
}

// HyperDebug drives IOB0, IOB1 and IOB3 again at the next reinit, before the
// chip is reset, so do not leave spi_host1 driving them.
static status_t release_pinmux(const dif_pinmux_t *pinmux) {
  const dif_pinmux_index_t kPads[] = {
      kTopEarlgreyPinmuxMioOutIob0, kTopEarlgreyPinmuxMioOutIob1,
      kTopEarlgreyPinmuxMioOutIob2, kTopEarlgreyPinmuxMioOutIob3};
  for (size_t i = 0; i < ARRAYSIZE(kPads); ++i) {
    TRY(dif_pinmux_output_select(pinmux, kPads[i],
                                 kTopEarlgreyPinmuxOutselConstantHighZ));
  }
  return OK_STATUS();
}
