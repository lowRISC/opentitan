// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_clkmgr.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/chip_info.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#if !OT_IS_ENGLISH_BREAKFAST
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#endif
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "otp_ctrl_regs.h"

/* These symbols are defined in
 * `opentitan/sw/device/lib/testing/test_rom/test_rom.ld`, and describes the
 * location of the flash header.
 */
extern char _rom_ext_virtual_start_address[];
extern char _rom_ext_virtual_size[];

/**
 * Type alias for the OTTF entry point.
 *
 * The entry point address obtained from the OTTF manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void ottf_entry_point(void);

static dif_clkmgr_t clkmgr;
static dif_flash_ctrl_state_t flash_ctrl;
static dif_pinmux_t pinmux;
static dif_rstmgr_t rstmgr;
static dif_uart_t uart0;
static dif_rv_core_ibex_t ibex;

/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param manifest Pointer to the current manifest.
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
static inline uintptr_t rom_ext_vma_get(const manifest_t *manifest,
                                        uintptr_t lma_addr) {
  return (lma_addr - (uintptr_t)manifest +
          (uintptr_t)_rom_ext_virtual_start_address);
}

// `test_in_rom = True` tests can override this symbol to provide their own
// rom tests. By default, it simply jumps into the OTTF's flash.
OT_WEAK
bool rom_test_main(void) {
#if !OT_IS_ENGLISH_BREAKFAST
  // Check the otp to see if execute should start
  uint32_t otp_val = abs_mmio_read32(
      TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
      OTP_CTRL_PARAM_CREATOR_SW_CFG_ROM_EXEC_EN_OFFSET);

  if (otp_val == 0) {
    test_status_set(kTestStatusInBootRomHalt);
    // Abort simply forever loops on a wait_for_interrupt;
    abort();
  }

  // Initialize Ibex cpuctrl (contains icache / security feature enablements).
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  uint32_t cpuctrl_otp_val = abs_mmio_read32(
      TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
      OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET);
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x3f, .index = 0},
      cpuctrl_otp_val);
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);
#endif

  // Initial sec_mmio, required by bootstrap and its dependencies.
  sec_mmio_init();

  // Configure the pinmux.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Initialize the flash.
  CHECK_DIF_OK(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  CHECK_DIF_OK(dif_flash_ctrl_start_controller_init(&flash_ctrl));
  CHECK_STATUS_OK(flash_ctrl_testutils_wait_for_init(&flash_ctrl));
#if !OT_IS_ENGLISH_BREAKFAST
  // Check the otp to see if flash scramble should be enabled.
  otp_val = abs_mmio_read32(
      TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
      OTP_CTRL_PARAM_CREATOR_SW_CFG_FLASH_DATA_DEFAULT_CFG_OFFSET);
  if (otp_val != 0) {
    dif_flash_ctrl_region_properties_t default_properties;
    CHECK_DIF_OK(dif_flash_ctrl_get_default_region_properties(
        &flash_ctrl, &default_properties));
    default_properties.scramble_en =
        bitfield_field32_read(otp_val, FLASH_CTRL_OTP_FIELD_SCRAMBLING);
    default_properties.ecc_en =
        bitfield_field32_read(otp_val, FLASH_CTRL_OTP_FIELD_ECC);
    default_properties.high_endurance_en =
        bitfield_field32_read(otp_val, FLASH_CTRL_OTP_FIELD_HE);
    CHECK_DIF_OK(dif_flash_ctrl_set_default_region_properties(
        &flash_ctrl, default_properties));
  }
#endif
  CHECK_DIF_OK(
      dif_flash_ctrl_set_flash_enablement(&flash_ctrl, kDifToggleEnabled));

  // Setup the UART for printing messages to the console.
  if (kDeviceType != kDeviceSimDV) {
    CHECK_DIF_OK(dif_uart_init(
        mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
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

  // Print the chip version information
  LOG_INFO("kChipInfo: scm_revision=%x", kChipInfo.scm_revision);

  // Skip sram_init for test_rom
  dif_rstmgr_reset_info_bitfield_t reset_reasons;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &reset_reasons));

#if !OT_IS_ENGLISH_BREAKFAST
  // Store the reset reason in retention RAM and clear the register.
  volatile retention_sram_t *ret_ram = retention_sram_get();
  ret_ram->reset_reasons = reset_reasons;
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

  // Write 0x54534554 (ASCII: TEST) to the end of the retention SRAM creator
  // area to be able to determine the type of ROM in tests.
  volatile uint32_t *creator_last_word =
      &ret_ram->reserved_creator[ARRAYSIZE(ret_ram->reserved_creator) - 1];
  *creator_last_word = TEST_ROM_IDENTIFIER;
#endif

  // Print the FPGA version-id.
  // This is guaranteed to be zero on all non-FPGA implementations.
  dif_rv_core_ibex_fpga_info_t fpga;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR), &ibex));
  CHECK_DIF_OK(dif_rv_core_ibex_read_fpga_info(&ibex, &fpga));
  if (fpga != 0) {
    LOG_INFO("TestROM:%08x", fpga);
  }

  // Enable clock jitter if requested.
  // The kJitterEnabled symbol defaults to false across all hardware platforms.
  // However, in DV simulation, it may be overridden via a backdoor write with
  // the plusarg: `+en_jitter=1`.
  if (kJitterEnabled) {
    CHECK_DIF_OK(dif_clkmgr_init(
        mmio_region_from_addr(TOP_EARLGREY_CLKMGR_AON_BASE_ADDR), &clkmgr));
    CHECK_DIF_OK(dif_clkmgr_jitter_set_enabled(&clkmgr, kDifToggleEnabled));
    LOG_INFO("Jitter is enabled");
  }

  if (bootstrap_requested() == kHardenedBoolTrue) {
    // This log statement is used to synchronize the rom and DV testbench
    // for specific test cases.
    LOG_INFO("Boot strap requested");

    rom_error_t bootstrap_err = bootstrap();
    if (bootstrap_err != kErrorOk) {
      LOG_ERROR("Bootstrap failed with status code: %08x",
                (uint32_t)bootstrap_err);
      // Currently the only way to recover is by a hard reset.
      test_status_set(kTestStatusFailed);
    }
  }
  CHECK_DIF_OK(
      dif_flash_ctrl_set_exec_enablement(&flash_ctrl, kDifToggleEnabled));

  // Always select slot a and enable address translation if manifest says to.
  const manifest_t *manifest =
      (const manifest_t *)TOP_EARLGREY_EFLASH_BASE_ADDR;
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  if (manifest->address_translation == kHardenedBoolTrue) {
    dif_rv_core_ibex_addr_translation_mapping_t addr_map = {
        .matching_addr = (uintptr_t)_rom_ext_virtual_start_address,
        .remap_addr = (uintptr_t)manifest,
        .size = (size_t)_rom_ext_virtual_size,
    };
    CHECK_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
        &ibex, kDifRvCoreIbexAddrTranslationSlot_0,
        kDifRvCoreIbexAddrTranslationDBus, addr_map));
    CHECK_DIF_OK(dif_rv_core_ibex_configure_addr_translation(
        &ibex, kDifRvCoreIbexAddrTranslationSlot_0,
        kDifRvCoreIbexAddrTranslationIBus, addr_map));
    CHECK_DIF_OK(dif_rv_core_ibex_enable_addr_translation(
        &ibex, kDifRvCoreIbexAddrTranslationSlot_0,
        kDifRvCoreIbexAddrTranslationDBus));
    CHECK_DIF_OK(dif_rv_core_ibex_enable_addr_translation(
        &ibex, kDifRvCoreIbexAddrTranslationSlot_0,
        kDifRvCoreIbexAddrTranslationIBus));
    entry_point = rom_ext_vma_get(manifest, entry_point);
  }

  // Jump to the OTTF in flash. Within the flash binary, it is the
  // responsibily of the OTTF to set up its own stack, and to never return.
  LOG_INFO("Test ROM complete, jumping to flash (addr: %x)!", entry_point);
  ((ottf_entry_point *)entry_point)();

  // If the flash image returns, we should abort anyway.
  abort();
}

void _boot_start(void) {
  test_status_set(kTestStatusInBootRom);
  test_status_set(rom_test_main() ? kTestStatusPassed : kTestStatusFailed);

  abort();
}
