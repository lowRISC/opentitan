// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/spi_flash_emulator.h"
#include "sw/device/lib/testing/spi_flash_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  kWakeupTimeMicros = 500000,
};
static dif_spi_device_handle_t spid;
static dif_pwrmgr_t pwrmgr;
static dif_aon_timer_t aon_timer;
static dif_rv_plic_t plic;
static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};
static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

static void enter_low_power(void) {
  uint64_t wkup_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_64_from_us(
      kWakeupTimeMicros, &wkup_cycles));
  CHECK_STATUS_OK(aon_timer_testutils_wakeup_config(&aon_timer, wkup_cycles));

  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg =
      kDifPwrmgrDomainOptionMainPowerInLowPower;

  LOG_INFO("SYNC: Entering lowpower mode");
  CHECK_STATUS_OK(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceFive, pwrmgr_domain_cfg));
  wait_for_interrupt();
  LOG_INFO("SYNC: Wakening up");
}

static status_t spi_flash_mode(void) {
  dif_spi_device_flash_id_t id = {
      .device_id = 0x2298,
      .manufacturer_id = 0x74,
      .continuation_code = 0x17,
      .num_continuation_code = 2,
  };
  TRY(dif_spi_device_set_flash_id(&spid, id));

  dif_spi_device_config_t spi_device_config = {
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModeFlashEmulation,
  };
  TRY(dif_spi_device_configure(&spid, spi_device_config));

  // Configure the READ_JEDEC_ID command (CMD_INFO_3).
  dif_spi_device_flash_command_t cmd = {
      .opcode = kSpiDeviceFlashOpReadJedec,
      .address_type = kDifSpiDeviceFlashAddrDisabled,
      .dummy_cycles = 0,
      .payload_io_type = kDifSpiDevicePayloadIoSingle,
      .payload_dir_to_host = false,
      .upload = false,
  };

  TRY(dif_spi_device_set_flash_command_slot(
      &spid, kSpiDeviceReadCommandSlotBase + 3, kDifToggleEnabled, cmd));

  LOG_INFO("SYNC: Flash mode");

  busy_spin_micros(1 * 1000 * 1000);

  return OK_STATUS();
}

bool test_main(void) {
  mmio_region_t addr;
  addr = mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR);
  CHECK_DIF_OK(dif_spi_device_init_handle(addr, &spid));

  addr = mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pwrmgr_init(addr, &pwrmgr));

  addr = mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_aon_timer_init(addr, &aon_timer));

  dif_pinmux_t pinmux;
  addr = mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR);
  CHECK_DIF_OK(dif_pinmux_init(addr, &pinmux));

  addr = mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(addr, &plic));

  // Enable all the AON interrupts used in this test.
  rv_plic_testutils_irq_range_enable(&plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);

  // Enable pwrmgr interrupt
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  LOG_INFO("Setting SPI_DIO1 to high when sleeping");
  CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio,
      kDifPinmuxSleepModeHigh));
  enter_low_power();

  LOG_INFO("Setting SPI_DIO1 to low when sleeping");
  CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio,
      kDifPinmuxSleepModeLow));
  enter_low_power();

  CHECK_DIF_OK(dif_pinmux_pad_sleep_clear_state(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio));
  CHECK_DIF_OK(dif_pinmux_pad_sleep_disable(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio));

  return status_ok(spi_flash_mode());
}

/**
 * External interrupt handler.
 */
void ottf_external_isr(uint32_t *exc_info) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}
