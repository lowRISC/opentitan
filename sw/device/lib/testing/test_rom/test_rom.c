// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/status.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/build_info.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifndef HAS_NVM
static inline void init_nvm(uint32_t nvm_default_cfg) {
  OT_DISCARD(nvm_default_cfg);
}
#else
#include "sw/device/lib/testing/nvm_testutils.h"

static inline void init_nvm(uint32_t nvm_default_cfg) {
  CHECK_STATUS_OK(nvm_testutils_rom_init(nvm_default_cfg));
}
#endif

#ifdef HAS_RETENTION_RAM
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#endif

#ifdef SKIP_BOOTSTRAP
static inline void run_bootstrap(void) {}
#else
#include "sw/device/silicon_creator/rom/bootstrap.h"

static inline void run_bootstrap(void) {
  if (bootstrap_requested() == kHardenedBoolTrue) {
    // This log statement is used to synchronize the rom and DV testbench
    // for specific test cases.
    LOG_INFO("Bootstrap requested");

    rom_error_t bootstrap_err = bootstrap();
    if (bootstrap_err != kErrorOk) {
      LOG_ERROR("Bootstrap failed with status code: %08x",
                (uint32_t)bootstrap_err);
      // Currently the only way to recover is by a hard reset.
      test_status_set(kTestStatusFailed);
    }
  }
}
#endif /* SKIP_BOOTSTRAP */

#ifndef HAS_OTP_CTRL
static inline uint32_t get_otp_ctrl_base(void) { return 0; }
static inline bool otp_rom_exec_en_is_zero(uint32_t otp_ctrl_base) {
  OT_DISCARD(otp_ctrl_base);
  return false;
}
static inline uint32_t get_otp_cpuctrl(uint32_t otp_ctrl_base) {
  OT_DISCARD(otp_ctrl_base);
  return 0;
}
static inline uint32_t get_otp_nvm_default_cfg(uint32_t otp_ctrl_base) {
  OT_DISCARD(otp_ctrl_base);
  return 0;
}
#else
#include "hw/top/dt/otp_ctrl.h"

#include "hw/top/otp_ctrl_regs.h"

static inline uint32_t get_otp_ctrl_base(void) {
  static_assert(kDtOtpCtrlCount == 1, "Expected one otp_ctrl IP");
  return dt_otp_ctrl_primary_reg_block(kDtOtpCtrlFirst);
}

static inline bool otp_rom_exec_en_is_zero(uint32_t otp_ctrl_base) {
  uint32_t otp_val =
      abs_mmio_read32(otp_ctrl_base + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                      OTP_CTRL_PARAM_CREATOR_SW_CFG_ROM_EXEC_EN_OFFSET);
  return (otp_val == 0);
}

static inline uint32_t get_otp_cpuctrl(uint32_t otp_ctrl_base) {
  return abs_mmio_read32(otp_ctrl_base + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                         OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET);
}

static inline uint32_t get_otp_nvm_default_cfg(uint32_t otp_ctrl_base) {
  return abs_mmio_read32(
      otp_ctrl_base + OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
      OTP_CTRL_PARAM_CREATOR_SW_CFG_NVM_DATA_DEFAULT_CFG_OFFSET);
}
#endif /* HAS_OTP_CTRL */

#ifndef HAS_PINMUX
static inline void init_pinmux(void) {}
#else
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/testing/pinmux_testutils.h"

static void init_pinmux(void) {
  static dif_pinmux_t pinmux;
  static_assert(kDtPinmuxCount == 1, "Expected one pinmux IP");
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxFirst, &pinmux));
  pinmux_testutils_init(&pinmux);
}
#endif /* HAS_PINMUX */

#ifndef HAS_UART
static inline void init_uart(void) {}
#else
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/print_uart.h"

static inline void init_uart(void) {
  static dif_uart_t uart0;

  // Setup the UART for printing messages to the console.
  static_assert(kDtUartCount >= 1, "Expected one or more uart IPs");
  CHECK_DIF_OK(dif_uart_init_from_dt(kDtUartFirst, &uart0));
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
#endif /* HAS_UART */

/* These symbols are defined in
 * `opentitan/sw/device/lib/testing/test_rom/test_rom.ld`, and describes the
 * location of the flash header and manifest.
 */
extern char _rom_ext_virtual_start_address[];
extern char _rom_ext_virtual_size[];
extern char _manifest_address[];

/**
 * Type alias for the OTTF entry point.
 *
 * The entry point address obtained from the OTTF manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void ottf_entry_point(void);

static dif_rstmgr_t rstmgr;
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
  // Check the otp to see if execute should start
  const uint32_t otp_ctrl_base = get_otp_ctrl_base();
  bool rom_exec_en_is_zero = otp_rom_exec_en_is_zero(otp_ctrl_base);
  if (rom_exec_en_is_zero) {
    test_status_set(kTestStatusInBootRomHalt);
    // Abort simply forever loops on a wait_for_interrupt;
    abort();
  }

#ifndef OPENTITAN_IS_ENGLISHBREAKFAST
  // Initialize Ibex cpuctrl (contains icache / security feature enablements).
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  uint32_t cpuctrl_otp_val = get_otp_cpuctrl(otp_ctrl_base);
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x3f, .index = 0},
      cpuctrl_otp_val);
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);
#endif

  // Initial sec_mmio, required by bootstrap and its dependencies.
  sec_mmio_init();

  init_pinmux();

  static_assert(kDtRstmgrCount == 1, "Expected one rstmgr IP");
  CHECK_DIF_OK(dif_rstmgr_init_from_dt(kDtRstmgrFirst, &rstmgr));

  // Initialize the NVM.
  {
    uint32_t nvm_default_cfg = get_otp_nvm_default_cfg(otp_ctrl_base);
    init_nvm(nvm_default_cfg);
  }

  if (kDeviceType != kDeviceSimDV) {
    init_uart();
  }

  // Print the chip version information
  LOG_INFO("kBuildInfo: scm_revision=%x", kBuildInfo.scm_revision);

  // Skip sram_init for test_rom
  dif_rstmgr_reset_info_bitfield_t reset_reasons;
  CHECK_DIF_OK(dif_rstmgr_reset_info_get(&rstmgr, &reset_reasons));

#ifdef HAS_RETENTION_RAM
  // Store the reset reason in retention RAM and clear the register.
  volatile retention_sram_t *ret_ram = retention_sram_get();
  ret_ram->creator.reset_reasons = reset_reasons;
  CHECK_DIF_OK(dif_rstmgr_reset_info_clear(&rstmgr));

  // Write 0x54534554 (ASCII: TEST) to the end of the retention SRAM creator
  // area to be able to determine the type of ROM in tests.
  volatile uint32_t *creator_last_word =
      &ret_ram->creator.reserved[ARRAYSIZE(ret_ram->creator.reserved) - 1];
  *creator_last_word = TEST_ROM_IDENTIFIER;
#endif

  // Print the FPGA version-id.
  // This is guaranteed to be zero on all non-FPGA implementations.
  dif_rv_core_ibex_fpga_info_t fpga;
  static_assert(kDtRvCoreIbexCount == 1, "Expected one rv_core_ibex IP");
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kDtRvCoreIbexFirst, &ibex));
  CHECK_DIF_OK(dif_rv_core_ibex_read_fpga_info(&ibex, &fpga));
  if (fpga != 0) {
    LOG_INFO("TestROM:%08x", fpga);
  }

  run_bootstrap();

  const manifest_t *manifest = (const manifest_t *)_manifest_address;
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  // Enable address translation if manifest says to
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

  // Jump to the OTTF in NVM. Within the flash/RRAM binary, it is the
  // responsibily of the OTTF to set up its own stack, and to never return.
  LOG_INFO("Test ROM complete, jumping to NVM (addr: %x)!", entry_point);
  ((ottf_entry_point *)entry_point)();

  // If the NVM image returns, we should abort anyway.
  abort();
}

void _boot_start(void) {
  test_status_set(kTestStatusInBootRom);
  test_status_set(rom_test_main() ? kTestStatusPassed : kTestStatusFailed);

  abort();
}
