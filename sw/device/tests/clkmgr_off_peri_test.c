// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/dif/dif_usbdev.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/nv_counter_testutils.h"
#include "sw/device/lib/testing/rstmgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "spi_host_regs.h"
#include "uart_regs.h"
#include "usbdev_regs.h"

/**
 * The peripherals used to test when the peri clocks are disabled are
 * bit 0: clk_io_div4_peri: uart0
 * bit 1: clk_io_div2_peri: spi_host1
 * bit 2: clk_io_peri: spi_host0
 * bit 3: clk_usb_peri: usbdev
 */

OTTF_DEFINE_TEST_CONFIG();

typedef struct peri_context {
  void (*csr_access)(void);  // The function causing a timeout.
  uint32_t address;          // The address causing a timeout.
} peri_context_t;

static dif_aon_timer_t aon_timer;
static dif_flash_ctrl_state_t flash_ctrl;
static dif_spi_host_t spi_host0;
static dif_spi_host_t spi_host1;
static dif_usbdev_t usbdev;
static dif_uart_t uart0;

OT_SET_BSS_SECTION(".non_volatile_scratch", uint64_t hung_data_addr[4];)

static void set_hung_address(dif_clkmgr_gateable_clock_t clock,
                             uint32_t value) {
  uint32_t addr =
      (uintptr_t)&hung_data_addr[clock] - TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
  uint32_t flash_word[2] = {value, 0};
  CHECK_STATUS_OK(flash_ctrl_testutils_write(
      &flash_ctrl, addr, 0, flash_word, kDifFlashCtrlPartitionTypeData, 2));
  CHECK(hung_data_addr[clock] == value, "Unexpected mismatch on read back");
  LOG_INFO("The expected hung address for clock %d is 0x%x at 0x%x", clock,
           value, addr);
}

static void uart0_csr_access(void) {
  dif_toggle_t state;
  CHECK_DIF_OK(dif_uart_irq_set_enabled(&uart0, kDifUartIrqTxWatermark,
                                        kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_uart_irq_get_enabled(&uart0, kDifUartIrqTxWatermark, &state));
  CHECK(state == kDifToggleEnabled);
}

static void spi_host0_csr_access(void) {
  dif_toggle_t state;
  CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host0, kDifSpiHostIrqSpiEvent,
                                            kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_spi_host_irq_get_enabled(&spi_host0, kDifSpiHostIrqSpiEvent, &state));
  CHECK(state == kDifToggleEnabled);
}

static void spi_host1_csr_access(void) {
  dif_toggle_t state;
  CHECK_DIF_OK(dif_spi_host_irq_set_enabled(&spi_host1, kDifSpiHostIrqSpiEvent,
                                            kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_spi_host_irq_get_enabled(&spi_host1, kDifSpiHostIrqSpiEvent, &state));
  CHECK(state == kDifToggleEnabled);
}

static void usbdev_csr_access(void) {
  CHECK_DIF_OK(dif_usbdev_irq_set_enabled(&usbdev, kDifUsbdevIrqPowered,
                                          kDifToggleEnabled));
  dif_toggle_t state;
  CHECK_DIF_OK(
      dif_usbdev_irq_get_enabled(&usbdev, kDifUsbdevIrqPowered, &state));
  CHECK(state == kDifToggleEnabled);
}

peri_context_t peri_context[kTopEarlgreyGateableClocksLast + 1] = {
    {uart0_csr_access,
     TOP_EARLGREY_UART0_BASE_ADDR + UART_INTR_ENABLE_REG_OFFSET},
    {spi_host1_csr_access,
     TOP_EARLGREY_SPI_HOST1_BASE_ADDR + SPI_HOST_INTR_ENABLE_REG_OFFSET},
    {spi_host0_csr_access,
     TOP_EARLGREY_SPI_HOST0_BASE_ADDR + SPI_HOST_INTR_ENABLE_REG_OFFSET},
    {usbdev_csr_access,
     TOP_EARLGREY_USBDEV_BASE_ADDR + USBDEV_INTR_ENABLE_REG_OFFSET}};

/**
 * Test that disabling a 'gateable' unit's clock causes the unit to become
 * unresponsive to CSR accesses. Configure a watchdog reset, and if it triggers
 * the test is successful.
 */
static void test_gateable_clocks_off(const dif_clkmgr_t *clkmgr,
                                     const dif_pwrmgr_t *pwrmgr,
                                     dif_clkmgr_gateable_clock_t clock) {
  // Make sure the clock for the unit is on.
  CHECK_DIF_OK(
      dif_clkmgr_gateable_clock_set_enabled(clkmgr, clock, kDifToggleEnabled));
  // Enable watchdog bite reset.
  CHECK_DIF_OK(dif_pwrmgr_set_request_sources(pwrmgr, kDifPwrmgrReqTypeReset,
                                              kDifPwrmgrResetRequestSourceTwo,
                                              kDifToggleEnabled));
  LOG_INFO("Testing peripheral clock %d", clock);

  // Bite after enough time has elapsed past the hung csr access.
  uint32_t bite_us = (kDeviceType == kDeviceSimDV) ? 400 : 800;
  uint32_t bite_cycles = 0;
  CHECK_STATUS_OK(
      aon_timer_testutils_get_aon_cycles_from_us(bite_us, &bite_cycles));
  LOG_INFO("Setting bite reset for %u us (%u cycles)", bite_us, bite_cycles);

  // Make sure the CSR is accessible before turning the clock off.
  (*peri_context[clock].csr_access)();
  LOG_INFO("CSR access was okay before disabling the clock");

  // Save the expected hung address to check against cpu_info's LAST_DATA_ADDR.
  set_hung_address(clock, peri_context[clock].address);
  // Set bite timer.
  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(&aon_timer, UINT32_MAX,
                                                      bite_cycles, false));
  // Disable the peripheral's clock.
  CHECK_DIF_OK(
      dif_clkmgr_gateable_clock_set_enabled(clkmgr, clock, kDifToggleDisabled));
  // Wait for the clock to really turn off.
  busy_spin_micros(100);
  // And issue the CSR access that will freeze and cause a reset.
  (*peri_context[clock].csr_access)();
}

bool test_main(void) {
  dif_clkmgr_t clkmgr;
  dif_pwrmgr_t pwrmgr;
  dif_rstmgr_t rstmgr;

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  CHECK_DIF_OK(dif_clkmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));

  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  // Initialize aon timer.
  CHECK_DIF_OK(dif_aon_timer_init(
      mmio_region_from_addr(TOP_EARLGREY_AON_TIMER_AON_BASE_ADDR), &aon_timer));

  // Initialize peripherals.
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST0_BASE_ADDR), &spi_host0));
  CHECK_DIF_OK(dif_spi_host_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_HOST1_BASE_ADDR), &spi_host1));
  CHECK_DIF_OK(dif_usbdev_init(
      mmio_region_from_addr(TOP_EARLGREY_USBDEV_BASE_ADDR), &usbdev));

  // Enable cpu dump capture.
  CHECK_DIF_OK(dif_rstmgr_cpu_info_set_enabled(&rstmgr, kDifToggleEnabled));

  // Enable raw flash access.
  CHECK_STATUS_OK(
      flash_ctrl_testutils_default_region_access(&flash_ctrl,
                                                 /*rd_en*/ true,
                                                 /*prog_en*/ true,
                                                 /*erase_en*/ true,
                                                 /*scramble_en*/ false,
                                                 /*ecc_en*/ false,
                                                 /*he_en*/ false));

  if (UNWRAP(rstmgr_testutils_is_reset_info(&rstmgr, kDifRstmgrResetInfoPor))) {
    CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

    // Starting clock.
    dif_clkmgr_gateable_clock_t clock = kTopEarlgreyGateableClocksIoDiv4Peri;
    uint32_t value = 0;
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &value));
    LOG_INFO("Next clock to test %d", value);

    test_gateable_clocks_off(&clkmgr, &pwrmgr, clock);

    // This should never be reached.
    LOG_ERROR("This is unreachable since a reset should have been triggered");
    return false;
  } else if (UNWRAP(rstmgr_testutils_is_reset_info(
                 &rstmgr, kDifRstmgrResetInfoWatchdog))) {
    dif_clkmgr_gateable_clock_t clock = {0};
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &clock));
    LOG_INFO("Got an expected watchdog reset when reading for clock %d", clock);

    size_t actual_size;
    CHECK_DIF_OK(dif_rstmgr_cpu_info_get_size(&rstmgr, &actual_size));
    // Verify the cpu crash dump.
    dif_rstmgr_cpu_info_dump_segment_t cpu_dump[DIF_RSTMGR_CPU_INFO_MAX_SIZE];
    size_t size_read;
    CHECK_DIF_OK(dif_rstmgr_cpu_info_dump_read(
        &rstmgr, cpu_dump, DIF_RSTMGR_CPU_INFO_MAX_SIZE, &size_read));
    CHECK(size_read <= DIF_RSTMGR_CPU_INFO_MAX_SIZE);
    CHECK(size_read == actual_size);
    LOG_INFO("EXC_ADDR       = 0x%x", cpu_dump[0]);
    LOG_INFO("EXC_PC         = 0x%x", cpu_dump[1]);
    LOG_INFO("LAST_DATA ADDR = 0x%x", cpu_dump[2]);
    LOG_INFO("NEXT_PC        = 0x%x", cpu_dump[3]);
    LOG_INFO("CURRENT_PC     = 0x%x", cpu_dump[4]);
    LOG_INFO("PREV_EXC_ADDR  = 0x%x", cpu_dump[5]);
    LOG_INFO("PREV_EXC_PC    = 0x%x", cpu_dump[6]);
    LOG_INFO("PREV_VALID     = 0x%x", cpu_dump[7]);
    uint64_t expected_hung_address = hung_data_addr[clock];
    CHECK(expected_hung_address < UINT32_MAX,
          "expected_hung_address must fit in uint32_t");
    LOG_INFO("The expected hung address = 0x%x",
             (uint32_t)expected_hung_address);
    CHECK(cpu_dump[2] == expected_hung_address, "Unexpected hung address");
    // Mark this clock as tested.
    CHECK_STATUS_OK(flash_ctrl_testutils_counter_increment(&flash_ctrl, 0));

    if (clock < kTopEarlgreyGateableClocksLast) {
      CHECK_STATUS_OK(flash_ctrl_testutils_counter_get(0, &clock));
      LOG_INFO("Next clock to test %d", clock);

      CHECK_STATUS_OK(rstmgr_testutils_pre_reset(&rstmgr));

      test_gateable_clocks_off(&clkmgr, &pwrmgr, clock);

      // This should never be reached.
      LOG_ERROR("This is unreachable since a reset should have been triggered");
      return false;
    } else {
      return true;
    }
  } else {
    dif_rstmgr_reset_info_bitfield_t reset_info;
    reset_info = rstmgr_testutils_reason_get();
    LOG_ERROR("Unexpected reset_info 0x%x", reset_info);
  }
  return false;
}
