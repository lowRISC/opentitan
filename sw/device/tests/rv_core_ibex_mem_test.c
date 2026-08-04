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
 * and executed. A location in the NVM data partition (flash or RRAM,
 * depending on the top) is written with a `jalr x0, 0(x1)` instruction, which
 * is again read from and executed. In both these cases execution is tested
 * with the instruction cache disabled and enabled.
 *
 * Two MMIO registers from two different devices are written to and read from.
 */

#include "sw/device/lib/arch/boot_stage.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/pmp.h"
#include "sw/device/lib/testing/nvm_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/base/chip.h"

#include "hw/top/aon_timer_regs.h"
#include "hw/top/rv_timer_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

enum {
  // Search within this ROM region to find `c.jr x1`, so execution can be
  // tested.
  kRomTestLocStart = TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR + 0x400,
  kRomTestLocEnd = TOP_EARLGREY_ROM_CTRL_ROM_BASE_ADDR + 0x500,
  kRomTestLocContent = 0x8082,

  // Number of pages allocated to the ROM_EXT. The same number of pages are
  // allocated at the begining of each data bank.
  kRomExtPageCount = CHIP_ROM_EXT_SIZE_MAX / NVM_BYTES_PER_PAGE,

  // The start page used by this test. Points to the start of the owner
  // partition in bank 1, otherwise known as owner partition B.
  kBank1StartPageNum = 256 + kRomExtPageCount,

  kNvmTestLoc = NVM_DATA_BASE_ADDR + kBank1StartPageNum * NVM_BYTES_PER_PAGE,
  // The ROM_EXT protects itself using regions 0-1.
  kNvmRegionNum = 2,
};

// The NVM test location is set to the encoding of `jalr x0, 0(x1)`
// so execution can be tested.
const uint32_t kNvmTestLocContent = 0x00008067;
void (*nvm_test_gadget)(void) = (void (*)(void))kNvmTestLoc;

volatile uint32_t *kMMIOTestLoc1 =
    (uint32_t *)(TOP_EARLGREY_RV_TIMER_BASE_ADDR +
                 RV_TIMER_COMPARE_LOWER0_0_REG_OFFSET);
const uint32_t kMMIOTestLoc1Content = 0x126d8c15;  // a random value

volatile uint32_t *kMMIOTestLoc2 =
    (uint32_t *)(TOP_EARLGREY_AON_TIMER_BASE_ADDR +
                 AON_TIMER_WKUP_THOLD_HI_REG_OFFSET);
const uint32_t kMMIOTestLoc2Content = 0xe4210e64;  // a random value

/**
 * Sets up the UART connection.
 */
static void setup_uart(void) {
  // DIF handles
  static dif_pinmux_t pinmux;

  // Initialise DIF handles
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_BASE_ADDR), &pinmux));

  // Initialise UART console.
  pinmux_testutils_init(&pinmux);
  ottf_console_init();
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
 * Sets up the NVM test location.
 */
static void setup_nvm(void) {
  // Create a PMP region for the NVM data partition.
  pmp_region_config_t config = {
      .lock = kPmpRegionLockLocked,
      .permissions = kPmpRegionPermissionsReadWriteExecute,
  };
  pmp_region_configure_napot_result_t result = pmp_region_configure_napot(
      8, config, NVM_DATA_BASE_ADDR, NVM_DATA_SIZE_BYTES);
  CHECK(result == kPmpRegionConfigureNapotOk,
        "Load configuration failed, error code = %d", result);
  // When running as ROM_EXT, ROM configures the NVM data partition to be
  // readonly. We need to execute so we need to unconfigure it.
  // This region is unconfigured by ROM_EXT so is no-op for silicon owner
  // stage.
  pmp_region_configure_result_t configure_result =
      pmp_region_configure_off(5, 0);
  CHECK(configure_result == kPmpRegionConfigureOk,
        "Load configuration failed, error code = %d", configure_result);

  // Initialise the NVM controller.
  CHECK_STATUS_OK(nvm_testutils_wait_for_init());

  CHECK_STATUS_OK(nvm_testutils_data_region_setup(
      kNvmRegionNum, kBank1StartPageNum, /*size=*/1, kPageReadWrite,
      (nvm_page_cfg_t){.scrambling = kMultiBitBool4False,
                       .ecc = kMultiBitBool4False,
                       .he = kMultiBitBool4False}));

  // Make the NVM data partition executable.
  CHECK_STATUS_OK(nvm_testutils_set_exec_enablement(true));

  // Write the wanted value to NVM.
  CHECK_STATUS_OK(nvm_testutils_data_write(kNvmTestLoc, &kNvmTestLocContent, 1,
                                           /*erase_before_write=*/true));
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

  LOG_INFO("Setting up the NVM test location.");
  setup_nvm();

  LOG_INFO("Check NVM load");
  load = *(volatile const uint32_t *)kNvmTestLoc;
  CHECK(load == kNvmTestLocContent,
        "The content of the NVM address was 0x%08x and not the expected value.",
        load);

  use_icache(false);
  LOG_INFO("Running an instruction from NVM with icache disabled.");
  nvm_test_gadget();
  use_icache(true);
  LOG_INFO("Running an instruction from NVM with icache enabled.");
  nvm_test_gadget();

  test_status_set(kTestStatusPassed);
  return true;
}
