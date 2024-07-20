// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"
#include "sw/ip/base/dif/dif_base.h"
#include "sw/ip/clkmgr/dif/dif_clkmgr.h"
#include "sw/ip/gpio/dif/dif_gpio.h"
#include "sw/ip/pinmux/dif/dif_pinmux.h"
#include "sw/ip/pinmux/test/utils/pinmux_testutils.h"
#include "sw/ip/rstmgr/dif/dif_rstmgr.h"
#include "sw/ip/rv_core_ibex/dif/dif_rv_core_ibex.h"
#include "sw/ip/uart/dif/dif_uart.h"
#include "sw/lib/sw/device/arch/device.h"
#include "sw/lib/sw/device/base/abs_mmio.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/csr.h"
#include "sw/lib/sw/device/base/mmio.h"
#include "sw/lib/sw/device/runtime/hart.h"
#include "sw/lib/sw/device/runtime/log.h"
#include "sw/lib/sw/device/runtime/print.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/chip_info.h"
#include "sw/lib/sw/device/silicon_creator/manifest.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"  // Generated.

/**
 * Type alias for the OTTF entry point.
 */
typedef void ottf_entry_point(void);

static dif_clkmgr_t clkmgr;
static dif_pinmux_t pinmux;
static dif_rstmgr_t rstmgr;
static dif_uart_t uart0;
static dif_rv_core_ibex_t ibex;

// `test_in_second_rom = True` tests can override this symbol to provide their
// own second stage ROM tests. By default, it simply jumps into the OTTF image
// in shared SRAM.
OT_WEAK
void _ottf_main(void) {
  const manifest_t *manifest =
      (const manifest_t *)TOP_DARJEELING_RAM_CTN_BASE_ADDR;
  uintptr_t entry_point = manifest_entry_point_get(manifest);

  LOG_INFO("Second stage test ROM complete, jumping to the test image @0x%x",
           entry_point);
  ((ottf_entry_point *)entry_point)();

  // If the test image returns, we should abort anyway.
  abort();
}

bool second_rom_test_main(void) {
  test_status_set(kTestStatusInBootRom);

  // Reset the MMIO counters
  sec_mmio_next_stage_init();

  // Configure the pinmux.
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_DARJEELING_PINMUX_AON_BASE_ADDR), &pinmux));
  pinmux_testutils_init(&pinmux);

  CHECK_DIF_OK(dif_rstmgr_init(
      mmio_region_from_addr(TOP_DARJEELING_RSTMGR_AON_BASE_ADDR), &rstmgr));

  // Setup the UART for printing messages to the console.
  if (kDeviceType != kDeviceSimDV) {
    CHECK_DIF_OK(dif_uart_init(
        mmio_region_from_addr(TOP_DARJEELING_UART0_BASE_ADDR), &uart0));
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

  // Print the FPGA version-id.
  // This is guaranteed to be zero on all non-FPGA implementations.
  dif_rv_core_ibex_fpga_info_t fpga;
  CHECK_DIF_OK(dif_rv_core_ibex_init(
      mmio_region_from_addr(TOP_DARJEELING_RV_CORE_IBEX_CFG_BASE_ADDR), &ibex));
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
        mmio_region_from_addr(TOP_DARJEELING_CLKMGR_AON_BASE_ADDR), &clkmgr));
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

  _ottf_main();

  // If the test image returns, we should abort anyway.
  abort();
}

void _boot_start(void) {
  test_status_set(kTestStatusInBootRom);
  test_status_set(second_rom_test_main() ? kTestStatusPassed
                                         : kTestStatusFailed);

  abort();
}
