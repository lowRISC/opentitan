// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/mask_rom.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/cfi.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify.h"
#include "sw/device/silicon_creator/mask_rom/boot_policy.h"
#include "sw/device/silicon_creator/mask_rom/mask_rom_epmp.h"
#include "sw/device/silicon_creator/mask_rom/primitive_bootstrap.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Table of forward branch Control Flow Integrity (CFI) counters.
 *
 * Columns: Name, Initital Value.
 *
 * Each counter is indexed by Name. The Initial Value is used to initialize the
 * counters with unique values with a good hamming distance. The values are
 * restricted to 11-bit to be able use immediate load instructions.
 */
// clang-format off
#define ROM_CFI_FUNC_COUNTERS_TABLE(X) \
  X(kCfiRomMain,    0xf05) \
  X(kCfiRomInit,    0x042) \
  X(kCfiRomVerify,  0x89d) \
  X(kCfiRomTryBoot, 0x4c7) \
  X(kCfiRomBoot,    0x0fb) \
// clang-format on

// Define counters and constant values required by the CFI counter macros.
CFI_DEFINE_COUNTERS(rom_counters, ROM_CFI_FUNC_COUNTERS_TABLE);

// Secure MMIO context.
//
// This is placed at a fixed location in memory within the .static_critical
// section. The location of this data is known to ROM_EXT.
__attribute__((section(".static_critical.sec_mmio_ctx")))
volatile sec_mmio_ctx_t sec_mmio_ctx;

// In-memory copy of the ePMP register configuration.
epmp_state_t epmp;
// Life cycle state of the chip.
lifecycle_state_t lc_state = (lifecycle_state_t)0;
// Boot data from flash.
boot_data_t boot_data = {0};

static inline rom_error_t mask_rom_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);
  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorInterrupt + mcause;
}

/**
 * Performs once-per-boot initialization of mask ROM modules and peripherals.
 */
static rom_error_t mask_rom_init(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomInit, 1);
  sec_mmio_init();
  // Initialize pinmux configuration so we can use the UART.
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  lc_state = lifecycle_state_get();

  // Re-initialize the watchdog timer.
  watchdog_init(lc_state);
  SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioInit);

  // Initialize the shutdown policy.
  HARDENED_RETURN_IF_ERROR(shutdown_init(lc_state));

  flash_ctrl_init();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit);

  // Initialize in-memory copy of the ePMP register configuration.
  mask_rom_epmp_state_init(&epmp);

  // Initialize the retention SRAM at power-on.
  //
  // The reset reason is treated as power-on if the POR bit is asserted
  // regardless of whether or not any other reset reason bits are set. This is
  // because we cannot guarantee that the retention SRAM was fully initialized
  // if the device was reset before the POR bit was cleared.
  //
  // TODO(lowRISC/opentitan#7887): once the retention SRAM is initialized the
  // reset reason should probably be saved into either main SRAM or the
  // retention SRAM and the reset reason register cleared.
  uint32_t reset_reasons = rstmgr_reason_get();
  if (bitfield_bit32_read(reset_reasons, kRstmgrReasonPowerOn)) {
    retention_sram_clear();
  }

  // Read boot data from flash
  HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, &boot_data));

  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(/*expected_check_count=*/1);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomInit, 2);
  return kErrorOk;
}

/**
 * Verifies a ROM_EXT.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * its `identifier` and `security_version` fields, and verifies its signature.
 *
 * @param Manifest of the ROM_EXT to be verified.
 * @param[out] flash_exec Value to write to the flash_ctrl EXEC register.
 * @return Result of the operation.
 */
static rom_error_t mask_rom_verify(const manifest_t *manifest,
                                   uint32_t *flash_exec) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 1);
  *flash_exec = 0;
  HARDENED_RETURN_IF_ERROR(boot_policy_manifest_check(manifest, &boot_data));

  const sigverify_rsa_key_t *key;
  HARDENED_RETURN_IF_ERROR(sigverify_rsa_key_get(
      sigverify_rsa_key_id_get(&manifest->modulus), lc_state, &key));

  hmac_sha256_init();
  // Invalidate the digest if the security version of the manifest is smaller
  // than the minimum required security version.
  if (launder32(manifest->security_version) <
      boot_data.min_security_version_rom_ext) {
    uint32_t extra_word = UINT32_MAX;
    hmac_sha256_update(&extra_word, sizeof(extra_word));
  }
  HARDENED_CHECK_GE(manifest->security_version,
                    boot_data.min_security_version_rom_ext);

  // Hash usage constraints.
  manifest_usage_constraints_t usage_constraints_from_hw;
  sigverify_usage_constraints_get(manifest->usage_constraints.selector_bits,
                                  &usage_constraints_from_hw);
  hmac_sha256_update(&usage_constraints_from_hw,
                     sizeof(usage_constraints_from_hw));
  // Hash the remaining part of the image.
  manifest_digest_region_t digest_region = manifest_digest_region_get(manifest);

  hmac_sha256_update(digest_region.start, digest_region.length);
  // Verify signature
  hmac_digest_t act_digest;
  hmac_sha256_final(&act_digest);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 2);
  return sigverify_rsa_verify(&manifest->signature, key, &act_digest, lc_state,
                              flash_exec);
}

/**
 * Boots a ROM_EXT.
 *
 * Note: This function should not return under normal conditions. Any returns
 * from this function must result in shutdown.
 *
 * @param manifest Manifest of the ROM_EXT to boot.
 * @param flash_exec Value to write to the flash_ctrl EXEC register.
 * @return rom_error_t Result of the operation.
 */
static rom_error_t mask_rom_boot(const manifest_t *manifest,
                                 uint32_t flash_exec) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 1);
  HARDENED_RETURN_IF_ERROR(keymgr_state_check(kKeymgrStateReset));
  keymgr_sw_binding_set(&manifest->binding_value, &manifest->binding_value);
  keymgr_creator_max_ver_set(manifest->max_key_version);
  SEC_MMIO_WRITE_INCREMENT(kKeymgrSecMmioSwBindingSet +
                           kKeymgrSecMmioCreatorMaxVerSet);

  // Check cached life cycle state against the value reported by hardware.
  lifecycle_state_t lc_state_check = lifecycle_state_get();
  if (launder32(lc_state_check) != lc_state) {
    return kErrorMaskRomBootFailed;
  }
  HARDENED_CHECK_EQ(lc_state_check, lc_state);

  // Check cached boot data.
  HARDENED_RETURN_IF_ERROR(boot_data_check(&boot_data));

  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(/*expected_check_count=*/3);

  // Unlock execution of ROM_EXT executable code (text) sections.
  HARDENED_RETURN_IF_ERROR(epmp_state_check(&epmp));
  mask_rom_epmp_unlock_rom_ext_rx(&epmp, manifest_code_region_get(manifest));
  HARDENED_RETURN_IF_ERROR(epmp_state_check(&epmp));

  // Enable execution of code from flash if signature is verified.
  flash_ctrl_exec_set(flash_exec);
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioExecSet);

  sec_mmio_check_counters(/*expected_check_count=*/4);

  // Jump to ROM_EXT entry point.
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 2);
  ((rom_ext_entry_point *)entry_point)();

  return kErrorMaskRomBootFailed;
}

/**
 * Attempts to boot ROM_EXTs in the order given by the boot policy module.
 *
 * @return Result of the last attempt.
 */
static rom_error_t mask_rom_try_boot(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 1);

  boot_policy_manifests_t manifests = boot_policy_manifests_get();
  uint32_t flash_exec = 0;

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 2, kCfiRomVerify);
  rom_error_t error = mask_rom_verify(manifests.ordered[0], &flash_exec);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 4);

  if (launder32(error) == kErrorOk) {
    HARDENED_CHECK_EQ(error, kErrorOk);
    CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomVerify, 3);
    CFI_FUNC_COUNTER_INIT(rom_counters, kCfiRomTryBoot);
    CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 1, kCfiRomBoot);
    HARDENED_RETURN_IF_ERROR(mask_rom_boot(manifests.ordered[0], flash_exec));
    return kErrorMaskRomBootFailed;
  }

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 5, kCfiRomVerify);
  HARDENED_RETURN_IF_ERROR(mask_rom_verify(manifests.ordered[1], &flash_exec));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 7);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomVerify, 3);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 8, kCfiRomBoot);
  HARDENED_RETURN_IF_ERROR(mask_rom_boot(manifests.ordered[1], flash_exec));
  return kErrorMaskRomBootFailed;
}

void mask_rom_main(void) {
  CFI_FUNC_COUNTER_INIT(rom_counters, kCfiRomMain);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomMain, 1, kCfiRomInit);
  SHUTDOWN_IF_ERROR(mask_rom_init());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomMain, 3);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomInit, 3);

  // TODO(lowrisc/opentitan#1513): Switch to EEPROM SPI device bootstrap
  // protocol.
  SHUTDOWN_IF_ERROR(primitive_bootstrap(lc_state));

  // `mask_rom_try_boot` will not return unless there is an error.
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomMain, 4, kCfiRomTryBoot);
  shutdown_finalize(mask_rom_try_boot());
}

void mask_rom_interrupt_handler(void) {
  shutdown_finalize(mask_rom_irq_error());
}

// We only need a single handler for all mask ROM interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the mask ROM,
// alias all interrupt handler symbols to the single handler.
void mask_rom_exception_handler(void)
    __attribute__((alias("mask_rom_interrupt_handler")));

void mask_rom_nmi_handler(void)
    __attribute__((alias("mask_rom_interrupt_handler")));
