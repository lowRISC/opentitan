// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#include <assert.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
              "This test assumes the target platform is little endian.");

OTTF_DEFINE_TEST_CONFIG();

dif_spi_host_t spi_host;

/**
 * Declared volatile because it is referenced in the main program flow as well
 * as the ISR.
 */
// Hold the test result.
static volatile status_t test_result;
// Used to sync the irs and the main thread.
static volatile dif_spi_host_irq_t irq_fired;
static dif_rv_plic_t plic;

enum {
  kHart = kTopEarlgreyPlicTargetIbex0,
};

/**
 * Provides external IRQ handling for this test.
 *
 * This function overrides the default OTTF external ISR.
 *
 * For each IRQ, it performs the following:
 * 1. Claims the IRQ fired (finds PLIC IRQ index).
 * 2. Checks that the index belongs to the expected peripheral.
 * 3. Checks that only the correct / expected IRQ is triggered.
 * 4. Clears the IRQ at the peripheral.
 * 5. Completes the IRQ service at PLIC.
 */
static status_t external_isr(void) {
  dif_rv_plic_irq_id_t plic_irq_id;
  TRY(dif_rv_plic_irq_claim(&plic, kHart, &plic_irq_id));
  LOG_INFO("%s: %d", __func__, plic_irq_id);

  top_earlgrey_plic_peripheral_t peripheral = (top_earlgrey_plic_peripheral_t)
      top_earlgrey_plic_interrupt_for_peripheral[plic_irq_id];
  TRY_CHECK(peripheral == kTopEarlgreyPlicPeripheralSpiHost0,
            "IRQ from incorrect peripheral: exp = %d(spi_host0), found = %d",
            kTopEarlgreyPlicPeripheralSpiHost0, peripheral);

  irq_fired = (dif_spi_host_irq_t)(plic_irq_id -
                                   (dif_rv_plic_irq_id_t)
                                       kTopEarlgreyPlicIrqIdSpiHost0Error);

  TRY(dif_spi_host_irq_acknowledge(&spi_host, irq_fired));

  // Complete the IRQ at PLIC.
  TRY(dif_rv_plic_irq_complete(&plic, kHart, plic_irq_id));
  return OK_STATUS();
}

void ottf_external_isr(void) { test_result = external_isr(); }

static status_t check_irq_eq(uint32_t irq) {
  irq_global_ctrl(false);
  if (irq_fired == UINT32_MAX) {
    wait_for_interrupt();
    irq_global_ctrl(true);
  }
  TRY_CHECK(irq_fired == irq);
  return OK_STATUS();
}

static status_t ready_event_irq(void) {
  enum { kDataSize = 250, kCommands = 5 };
  static_assert(kDataSize % kCommands == 0, "Must be multiple.");

  uint8_t data[kDataSize];
  memset(data, 0xA5, kDataSize);
  dif_spi_host_status_t status;

  irq_fired = UINT32_MAX;
  TRY(dif_spi_host_event_set_enabled(&spi_host, kDifSpiHostEvtReady, true));

  TRY(dif_spi_host_get_status(&spi_host, &status));
  TRY_CHECK(status.ready);
  TRY_CHECK(!status.active);

  // Overwhelm the cmd fifo to make the `STATUS.ready` goes low.
  TRY(dif_spi_host_fifo_write(&spi_host, data, kDataSize));
  for (size_t i = 0; i < kCommands; ++i) {
    TRY(dif_spi_host_write_command(&spi_host, kDataSize / kCommands,
                                   kDifSpiHostWidthStandard,
                                   kDifSpiHostDirectionTx, true));
  }

  TRY(dif_spi_host_get_status(&spi_host, &status));
  TRY_CHECK(!status.ready);
  TRY_CHECK(status.active);

  // Wait for the event irq and check that it was triggered by `STATUS.ready`.
  TRY(check_irq_eq(kDifSpiHostIrqSpiEvent));
  TRY(dif_spi_host_get_status(&spi_host, &status));
  TRY_CHECK(status.ready);

  TRY(dif_spi_host_event_set_enabled(&spi_host, kDifSpiHostEvtReady, false));
  return OK_STATUS();
}

static status_t active_event_irq(void) {
  uint8_t data[256];
  memset(data, 0xA5, sizeof(data));

  irq_fired = UINT32_MAX;
  TRY(dif_spi_host_event_set_enabled(&spi_host, kDifSpiHostEvtIdle, true));

  dif_spi_host_status_t status;
  TRY(dif_spi_host_get_status(&spi_host, &status));
  TRY_CHECK(!status.active);

  // Issue a command and check that the `STATUS.active` goes low.
  TRY(dif_spi_host_fifo_write(&spi_host, data, sizeof(data)));
  TRY(dif_spi_host_write_command(&spi_host, sizeof(data),
                                 kDifSpiHostWidthStandard,
                                 kDifSpiHostDirectionTx, true));
  TRY(dif_spi_host_get_status(&spi_host, &status));
  TRY_CHECK(status.active);

  // Wait for the event irq and check that it was triggered by `STATUS.active`.
  check_irq_eq(kDifSpiHostIrqSpiEvent);
  TRY(dif_spi_host_get_status(&spi_host, &status));
  TRY_CHECK(!status.active);

  TRY(dif_spi_host_event_set_enabled(&spi_host, kDifSpiHostEvtIdle, false));

  return OK_STATUS();
}

static status_t test_init(void) {
  mmio_region_t base_addr;

  base_addr = mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR);
  TRY(dif_spi_host_init(base_addr, &spi_host));

  TRY(dif_spi_host_configure(
      &spi_host, (dif_spi_host_config_t){
                     .spi_clock = 1000000,
                     .peripheral_clock_freq_hz = kClockFreqPeripheralHz,
                     .rx_watermark = 128,
                     .tx_watermark = 64,
                 }));
  TRY(dif_spi_host_output_set_enabled(&spi_host, true));

  base_addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  TRY(dif_rv_plic_init(base_addr, &plic));

  rv_plic_testutils_irq_range_enable(&plic, kHart, kDifSpiHostIrqSpiEvent,
                                     kTopEarlgreyPlicIrqIdSpiHost0SpiEvent);

  dif_spi_host_irq_state_snapshot_t spi_host_irqs =
      (dif_spi_host_irq_state_snapshot_t)UINT_MAX;
  TRY(dif_spi_host_irq_restore_all(&spi_host, &spi_host_irqs));

  irq_global_ctrl(true);
  irq_external_ctrl(true);
  return OK_STATUS();
}

bool test_main(void) {
  CHECK_STATUS_OK(test_init());
  test_result = OK_STATUS();
  EXECUTE_TEST(test_result, active_event_irq);
  EXECUTE_TEST(test_result, ready_event_irq);
  return status_ok(test_result);
}
