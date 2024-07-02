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

static dif_gpio_t gpio;
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

static status_t enter_low_power(void) {
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg =
      kDifPwrmgrDomainOptionIoClockInLowPower |
      kDifPwrmgrDomainOptionMainPowerInLowPower;
  // Wait for the host signal that the device can sleep.
  bool sleep = false;
  do {
    CHECK_DIF_OK(dif_gpio_read(&gpio, 0, &sleep));
  } while (!sleep);

  irq_global_ctrl(false);
  LOG_INFO("SYNC: Sleeping");
  TRY(pwrmgr_testutils_enable_low_power(
      &pwrmgr, kDifPwrmgrWakeupRequestSourceThree, pwrmgr_domain_cfg));
  wait_for_interrupt();

  // Sometimes execution continues after the wfi while the core is preparing to
  // enter low power mode. In that case we loop checking if the host requested a
  // sleep. If not we loop until core enters low power mode.
  do {
    CHECK_DIF_OK(dif_gpio_read(&gpio, 0, &sleep));
  } while (sleep);
  irq_global_ctrl(true);
  LOG_INFO("SYNC: Awaked");
  return OK_STATUS();
}

static status_t configure_spi_flash_mode(void) {
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

  addr = mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR);
  CHECK_DIF_OK(dif_gpio_init(addr, &gpio));
  CHECK_DIF_OK(dif_gpio_output_set_enabled_all(&gpio, 0x1));

  // Enable all the AON interrupts used to wake up the core.
  rv_plic_testutils_irq_range_enable(&plic, kTopEarlgreyPlicTargetIbex0,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                     kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
  CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));

  irq_global_ctrl(true);
  irq_external_ctrl(true);

  dif_pinmux_index_t detector = 0;
  dif_pinmux_wakeup_config_t wakeup_cfg = {
      .mode = kDifPinmuxWakeupModeNegativeEdge,
      .signal_filter = false,
      .pad_type = kDifPinmuxPadKindMio,
      .pad_select = kTopEarlgreyPinmuxInselIoa8,
  };
  CHECK_DIF_OK(
      dif_pinmux_wakeup_detector_enable(&pinmux, detector, wakeup_cfg));

  // Phase1: spi sleep test
  LOG_INFO("Setting SPI_DIO1 to high when sleeping");
  CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio,
      kDifPinmuxSleepModeHigh));
  LOG_INFO("Use IOA7 to let host know when sleep is active.");
  CHECK_DIF_OK(dif_pinmux_input_select(&pinmux,
                                       kTopEarlgreyPinmuxPeripheralInGpioGpio0,
                                       kTopEarlgreyPinmuxInselIoa8));
  CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(&pinmux, kTopEarlgreyMuxedPadsIoa7,
                                           kDifPinmuxPadKindMio,
                                           kDifPinmuxSleepModeLow));
  enter_low_power();
  CHECK_DIF_OK(dif_pinmux_pad_sleep_clear_state(
      &pinmux, kTopEarlgreyMuxedPadsIoa7, kDifPinmuxPadKindMio));

  LOG_INFO("Setting SPI_DIO1 to low when sleeping");
  CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio,
      kDifPinmuxSleepModeLow));

  CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(&pinmux, kTopEarlgreyMuxedPadsIoa7,
                                           kDifPinmuxPadKindMio,
                                           kDifPinmuxSleepModeLow));
  enter_low_power();
  CHECK_DIF_OK(dif_pinmux_pad_sleep_clear_state(
      &pinmux, kTopEarlgreyMuxedPadsIoa7, kDifPinmuxPadKindMio));

  CHECK_DIF_OK(dif_pinmux_pad_sleep_clear_state(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio));
  CHECK_DIF_OK(dif_pinmux_pad_sleep_disable(
      &pinmux, kTopEarlgreyDirectPadsSpiDeviceSd1, kDifPinmuxPadKindDio));

  // Phase2: spi wake-up test
  // Configures to wake up when the spi cs goes low.
  wakeup_cfg = (dif_pinmux_wakeup_config_t){
      .mode = kDifPinmuxWakeupModeAnyEdge,
      .signal_filter = false,
      .pad_type = kDifPinmuxPadKindDio,
      .pad_select = kTopEarlgreyDirectPadsSpiHost0Csb,
  };
  CHECK_DIF_OK(
      dif_pinmux_wakeup_detector_enable(&pinmux, detector, wakeup_cfg));
  configure_spi_flash_mode();
  enter_low_power();
  CHECK_DIF_OK(dif_pinmux_wakeup_detector_disable(&pinmux, detector));

  busy_spin_micros(2 * 1000 * 1000);

  return true;
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
