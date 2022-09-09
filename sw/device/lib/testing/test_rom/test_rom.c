// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
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
#include "sw/device/lib/testing/test_rom/chip_info.h"  // Generated.
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

/**
 * This symbol is defined in `sw/device/lib/testing/test_rom/test_rom.ld`,
 * and describes the location of the flash header.
 *
 * The actual contents are not defined by the ROM, but rather
 * by the flash binary: see `sw/device/lib/testing/test_framework/ottf.ld`
 * for that.
 */
extern const char _manifest[];

/**
 * Type alias for the OTTF entry point.
 *
 * The entry point address obtained from the OTTF manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void ottf_entry(void);

static dif_clkmgr_t clkmgr;
static dif_flash_ctrl_state_t flash_ctrl;
static dif_pinmux_t pinmux;
static dif_rstmgr_t rstmgr;
static dif_uart_t uart0;
static dif_rv_core_ibex_t ibex;

// `test_in_rom = True` tests can override this symbol to provide their own
// rom tests. By default, it simply jumps into the OTTF's flash.
OT_WEAK
bool rom_test_main(void) {
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
  flash_ctrl_testutils_wait_for_init(&flash_ctrl);
  CHECK_DIF_OK(
      dif_flash_ctrl_set_flash_enablement(&flash_ctrl, kDifToggleEnabled));

  // Setup the UART for printing messages to the console.
  if (kDeviceType != kDeviceSimDV) {
    CHECK_DIF_OK(dif_uart_init(
        mmio_region_from_addr(TOP_EARLGREY_UART0_BASE_ADDR), &uart0));
    CHECK_DIF_OK(
        dif_uart_configure(&uart0, (dif_uart_config_t){
                                       .baudrate = kUartBaudrate,
                                       .clk_freq_hz = kClockFreqPeripheralHz,
                                       .parity_enable = kDifToggleDisabled,
                                       .parity = kDifUartParityEven,
                                   }));
    base_uart_stdout(&uart0);
  }

  // Print the chip version information
  LOG_INFO("%s", chip_info);

  // Skip sram_init for test_rom
  dif_rstmgr_reset_info_bitfield_t reset_reasons;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &reset_reasons));

  // Store the reset reason in retention RAM and clear the register.
  retention_sram_get()->reset_reasons = reset_reasons;
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

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

  // TODO(lowrisc/opentitan:#10712): setup Ibex address translation

  // Jump to the OTTF in flash. Within the flash binary, it is the responsibily
  // of the OTTF to set up its own stack, and to never return.
  uintptr_t entry_point =
      manifest_entry_point_get((const manifest_t *)_manifest);
  LOG_INFO("Test ROM complete, jumping to flash!");
  ((ottf_entry *)entry_point)();

  // If the flash image returns, we should abort anyway.
  abort();
}

void _boot_start(void) {
  test_status_set(kTestStatusInBootRom);
  test_status_set(rom_test_main() ? kTestStatusPassed : kTestStatusFailed);

  abort();
}
