// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
/**
 * RV Core Ibex Memory Smoke Test
 *
 * This test runs checks access to each kind of memory from the Ibex.
 *
 * It is expected to run from SRAM,
 * so will fail if SRAM read, write or execution does.
 *
 * A known location in ROM which contains a `c.jr x1` instruction is read from
 * and executed. A location is flash is written with a `jalr x0, 0(x1)`
 * instruction, which is a again read from and executed. In both these cases
 * execution is tested with the instruction cache disabled and enabled.
 *
 * Two MMIO registers from two different devices are written to and read from.
 */

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/pmp.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

#include "flash_ctrl_regs.h"
#include "hw/ip/pwm/data/pwm_regs.h"
#include "hw/ip/rv_timer/data/rv_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  // Search within this ROM region to find `c.jr x1`, so execution can be
  // tested.
  kRomTestLocStart = TOP_EARLGREY_ROM_BASE_ADDR + 0x400,
  kRomTestLocEnd = TOP_EARLGREY_ROM_BASE_ADDR + 0x500,
  kRomTestLocContent = 0x8082,

  // Number of bytes per page.
  kFlashBytesPerPage = FLASH_CTRL_PARAM_BYTES_PER_PAGE,

  // Number of pages allocated to the ROM_EXT. The same number of pages are
  // allocated at the begining of each data bank.
  kRomExtPageCount = CHIP_ROM_EXT_SIZE_MAX / kFlashBytesPerPage,

  // The start page used by this test. Points to the start of the owner
  // partition in bank 1, otherwise known as owner partition B.
  kBank1StartPageNum = 256 + kRomExtPageCount,

  kFlashTestLoc = TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR +
                  kBank1StartPageNum * kFlashBytesPerPage,
};

// The flash test location is set to the encoding of `jalr x0, 0(x1)`
// so execution can be tested.
const uint32_t kFlashTestLocContent = 0x00008067;
void (*flash_test_gadget)(void) = (void (*)(void))kFlashTestLoc;

volatile uint32_t *kMMIOTestLoc1 =
    (uint32_t *)(TOP_EARLGREY_RV_TIMER_BASE_ADDR +
                 RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET);
const uint32_t kMMIOTestLoc1Content = 0x126d8c15;  // a random value

volatile uint32_t *kMMIOTestLoc2 =
    (uint32_t *)(TOP_EARLGREY_PWM_AON_BASE_ADDR + PWM_DUTY_CYCLE_0_REG_OFFSET);
const uint32_t kMMIOTestLoc2Content = 0xe4210e64;  // a random value

/**
 * Sets up the UART connection.
 */
static void setup_uart(void) {
  // DIF handles
  static dif_uart_t uart0;
  static dif_pinmux_t pinmux;

  // Initialise DIF handles
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_uart_init(
      mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));

  // Initialise UART console.
  pinmux_testutils_init(&pinmux);
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &uart0, (dif_uart_config_t){
                  .baudrate = (uint32_t)kUartBaudrate,
                  .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                  .parity_enable = kDifToggleDisabled,
                  .parity = kDifUartParityEven,
                  .tx_enable = kDifToggleEnabled,
                  .rx_enable = kDifToggleEnabled,
              }));
  base_uart_stdout(&uart0);
}

/**
 * Enable/disable icache
 *
 * @param enable whether or not icache should be enabled
 */
static void use_icache(bool enable) {
  if (enable) {
    CSR_SET_BITS(CSR_REG_CPUCTRL, 1);
  } else {
    CSR_CLEAR_BITS(CSR_REG_CPUCTRL, 1);
  }
  uint32_t csr;
  CSR_READ(CSR_REG_CPUCTRL, &csr);
  CHECK((csr & 1) == enable, "Couldn't enable or disable icache.");
}

/**
 * Sets up the flash test location.
 */
static void setup_flash(void) {
  // Create a PMP region for the flash
  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsReadWriteExecute,
  };
  pmp_region_configure_napot_result_t result = pmp_region_configure_napot(
      8, config, TOP_EARLGREY_EFLASH_BASE_ADDR, TOP_EARLGREY_EFLASH_SIZE_BYTES);
  CHECK(result == kPmpRegionConfigureNapotOk,
        "Load configuration failed, error code = %d", result);
  // When running as ROM_EXT, ROM configures the flash memory to be readonly.
  // We need to execute so we need to unconfigure it.
  // This region is unconfigured by ROM_EXT so is no-op for silicon owner stage.
  pmp_region_configure_result_t configure_result =
      pmp_region_configure_off(5, 0);
  CHECK(configure_result == kPmpRegionConfigureOk,
        "Load configuration failed, error code = %d", configure_result);

  // Initialise the flash controller.
  dif_flash_ctrl_state_t flash_ctrl;
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));

  CHECK_STATUS_OK(flash_ctrl_testutils_wait_for_init(&flash_ctrl));

  dif_flash_ctrl_region_properties_t region_properties = {
      .rd_en = kMultiBitBool4True,
      .prog_en = kMultiBitBool4True,
      .erase_en = kMultiBitBool4True,
      .scramble_en = kMultiBitBool4False,
      .ecc_en = kMultiBitBool4False,
      .high_endurance_en = kMultiBitBool4False};
  dif_flash_ctrl_data_region_properties_t data_region = {
      .base = kBank1StartPageNum, .size = 0x1, .properties = region_properties};

  CHECK_DIF_OK(
      dif_flash_ctrl_set_data_region_properties(&flash_ctrl, 0, data_region));
  CHECK_DIF_OK(dif_flash_ctrl_set_data_region_enablement(&flash_ctrl, 0,
                                                         kDifToggleEnabled));

  // Make flash executable
  CHECK_DIF_OK(
      dif_flash_ctrl_set_exec_enablement(&flash_ctrl, kDifToggleEnabled));

  // Write the wanted value to flash
  CHECK_STATUS_OK(flash_ctrl_testutils_erase_and_write_page(
      /*flash_state=*/&flash_ctrl,
      /*byte_address=*/kFlashTestLoc,
      /*partition_id=*/0,
      /*data=*/&kFlashTestLocContent,
      /*partition_type=*/kDifFlashCtrlPartitionTypeData,
      /*word_count=*/1));
}

/**
 * The entry point of the SRAM test.
 */
bool test_main(void) {
  setup_uart();

  // ROM access is blocked in the silicon owner stage.
  if (kBootStage != kBootStageOwner) {
    LOG_INFO("Testing Load from ROM Location.");

    // For the execution test we a specific `c.jr x1` (i.e. function return)
    // instruction. Since the address can vary between ROM builds, we scan a
    // small region to find it.
    volatile uint16_t *test_loc;
    for (test_loc = (uint16_t *)kRomTestLocStart;
         test_loc < (uint16_t *)kRomTestLocEnd; test_loc++) {
      if (*test_loc == kRomTestLocContent) {
        break;
      }
    }
    CHECK(test_loc != (uint16_t *)kRomTestLocEnd,
          "Couldn't find the expected content in ROM test location.");
    LOG_INFO("Found the expected content at 0x%p", test_loc);
    void (*rom_test_gadget)(void) = (void (*)(void))test_loc;

    use_icache(false);
    LOG_INFO("Running an instruction from ROM with icache disabled.");
    rom_test_gadget();

    use_icache(true);
    LOG_INFO("Running an instruction from ROM with icache enabled.");
    rom_test_gadget();
  }

  LOG_INFO("Testing Store to and Load from MMIO Location 1");
  *kMMIOTestLoc1 = kMMIOTestLoc1Content;
  uint32_t load = *kMMIOTestLoc1;
  CHECK(
      load == kMMIOTestLoc1Content,
      "The content of the MMIO address was 0x%08x and not the expected value.",
      load);

  LOG_INFO("Testing Store to and Load from MMIO Location 2");
  *kMMIOTestLoc2 = kMMIOTestLoc2Content;
  load = *kMMIOTestLoc2;
  CHECK(
      load == kMMIOTestLoc2Content,
      "The content of the MMIO address was 0x%08x and not the expected value.",
      load);

  LOG_INFO("Setting up the flash test location.");
  setup_flash();

  LOG_INFO("Check flash load");
  load = *(volatile const uint32_t *)kFlashTestLoc;
  CHECK(
      load == kFlashTestLocContent,
      "The content of the Flash address was 0x%08x and not the expected value.",
      load);

  use_icache(false);
  LOG_INFO("Running an instruction from Flash with icache disabled.");
  flash_test_gadget();
  use_icache(true);
  LOG_INFO("Running an instruction from Flash with icache enabled.");
  flash_test_gadget();

  test_status_set(kTestStatusPassed);
  return true;
}
