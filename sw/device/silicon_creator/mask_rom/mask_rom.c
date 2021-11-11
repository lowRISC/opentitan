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
#include "sw/device/lib/pinmux.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/log.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify.h"
#include "sw/device/silicon_creator/mask_rom/boot_policy.h"
#include "sw/device/silicon_creator/mask_rom/mask_rom_epmp.h"
#include "sw/device/silicon_creator/mask_rom/primitive_bootstrap.h"
#include "sw/device/silicon_creator/mask_rom/sigverify_keys.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Secure MMIO context.
//
// This is placed at a fixed location in memory within the .static_critical
// section. The location of this data is known to ROM_EXT.
__attribute__((section(".static_critical.sec_mmio_ctx")))  //
volatile sec_mmio_ctx_t sec_mmio_ctx;

// In-memory copy of the ePMP register configuration.
epmp_state_t epmp;
// Life cycle state of the chip.
lifecycle_state_t lc_state = kLcStateProd;

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
static void mask_rom_init(void) {
  sec_mmio_init(shutdown_finalize);
  // Initialize the shutdown policy according to lifecycle state.
  lc_state = lifecycle_state_get();
  shutdown_init(lc_state);
  flash_ctrl_init();
  // Initiaize in-memory copy of the ePMP register configuration.
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

  // Initialize pinmux configuration so we can use the UART.
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  // TODO(lowRISC/opentitan#8536): Integrate RND driver.
  sec_mmio_check_values(/*rnd_offset=*/0);
  sec_mmio_check_counters(/*expected_check_count=*/1);
}

/**
 * Verifies a ROM_EXT.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * its `identifier` and `security_version` fields, and verifies its signature.
 *
 * @param Manifest of the ROM_EXT to be verified.
 * @return Result of the operation.
 */
static rom_error_t mask_rom_verify(const manifest_t *manifest) {
  RETURN_IF_ERROR(boot_policy_manifest_check(manifest));

  const sigverify_rsa_key_t *key;
  RETURN_IF_ERROR(sigverify_rsa_key_get(
      sigverify_rsa_key_id_get(&manifest->modulus), lc_state, &key));

  hmac_sha256_init();
  // Hash usage constraints.
  manifest_usage_constraints_t usage_constraints_from_hw;
  sigverify_usage_constraints_get(manifest->usage_constraints.selector_bits,
                                  &usage_constraints_from_hw);
  RETURN_IF_ERROR(hmac_sha256_update(&usage_constraints_from_hw,
                                     sizeof(usage_constraints_from_hw)));
  // Hash the remaining part of the image.
  manifest_digest_region_t digest_region = manifest_digest_region_get(manifest);
  RETURN_IF_ERROR(
      hmac_sha256_update(digest_region.start, digest_region.length));
  // Verify signature
  hmac_digest_t act_digest;
  RETURN_IF_ERROR(hmac_sha256_final(&act_digest));
  RETURN_IF_ERROR(
      sigverify_rsa_verify(&manifest->signature, key, &act_digest, lc_state));
  return kErrorOk;
}

/**
 * Boots a ROM_EXT.
 *
 * Note: This function should not return under normal conditions. Any returns
 * from this function must result in shutdown.
 *
 * @param manifest Manifest of the ROM_EXT to boot.
 * @return rom_error_t Result of the operation.
 */
static rom_error_t mask_rom_boot(const manifest_t *manifest) {
  RETURN_IF_ERROR(keymgr_state_check(kKeymgrStateReset));
  keymgr_sw_binding_set(&manifest->binding_value, &manifest->binding_value);
  keymgr_creator_max_ver_set(manifest->max_key_version);

  // Enable execution of code from flash.
  flash_ctrl_exec_set(kFlashCtrlExecEnable);

  // TODO(lowRISC/opentitan#8536): Integrate RND driver.
  sec_mmio_check_values(/*rnd_offset=*/0);
  sec_mmio_check_counters(/*expected_check_count=*/3);

  // Unlock execution of ROM_EXT executable code (text) sections.
  RETURN_IF_ERROR(epmp_state_check(&epmp));
  mask_rom_epmp_unlock_rom_ext_rx(&epmp, manifest_code_region_get(manifest));
  RETURN_IF_ERROR(epmp_state_check(&epmp));

  // Jump to ROM_EXT entry point.
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  log_printf("rom_ext_entry: 0x%x\r\n", (unsigned int)entry_point);
  ((rom_ext_entry_point *)entry_point)();

  return kErrorMaskRomBootFailed;
}

/**
 * Attempts to boot ROM_EXTs in the order given by the boot policy module.
 *
 * @return Result of the last attempt.
 */
static rom_error_t mask_rom_try_boot(void) {
  boot_policy_manifests_t manifests = boot_policy_manifests_get();
  rom_error_t error = kErrorMaskRomBootFailed;
  for (size_t i = 0; i < ARRAYSIZE(manifests.ordered); ++i) {
    error = mask_rom_verify(manifests.ordered[i]);
    if (error != kErrorOk) {
      continue;
    }
    // Boot fails if a verified ROM_EXT cannot be booted.
    RETURN_IF_ERROR(mask_rom_boot(manifests.ordered[i]));
    // `mask_rom_boot()` should never return `kErrorOk`, but if it does
    // we must shut down the chip instead of trying the next ROM_EXT.
    return kErrorMaskRomBootFailed;
  }
  return error;
}

void mask_rom_main(void) {
  mask_rom_init();

  // TODO(lowrisc/opentitan#7894): What (if anything) should we print at
  // startup?
  log_printf("OpenTitan: \"version-tag\"\r\n");
  log_printf("lc_state: %s\r\n", lifecycle_state_name[lc_state]);

  // TODO(lowrisc/opentitan#1513): Switch to EEPROM SPI device bootstrap
  // protocol.
  rom_error_t error = primitive_bootstrap();
  if (error != kErrorOk) {
    shutdown_finalize(error);
  }
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
