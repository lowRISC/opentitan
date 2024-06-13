// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom.h"

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/static_critical_version.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/cfi.h"
#include "sw/device/silicon_creator/lib/chip_info.h"
#include "sw/device/silicon_creator/lib/drivers/alert.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/pwrmgr.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom/boot_policy.h"
#include "sw/device/silicon_creator/rom/boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom/bootstrap.h"
#include "sw/device/silicon_creator/rom/rom_epmp.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_ecdsa_p256.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"
#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"

#include "hmac_regs.h"  // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "otp_ctrl_regs.h"
#include "rstmgr_regs.h"

/**
 * Table of forward branch Control Flow Integrity (CFI) counters.
 *
 * Columns: Name, Initital Value.
 *
 * Each counter is indexed by Name. The Initial Value is used to initialize the
 * counters with unique values with a good hamming distance. The values are
 * restricted to 11-bit to be able use immediate load instructions.

 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 6 -n 11 \
 *     -s 1630646358 --language=c
 *
 * Minimum Hamming distance: 6
 * Maximum Hamming distance: 8
 * Minimum Hamming weight: 5
 * Maximum Hamming weight: 8
 */
// clang-format off
#define ROM_CFI_FUNC_COUNTERS_TABLE(X) \
  X(kCfiRomMain,         0x14b) \
  X(kCfiRomInit,         0x7dc) \
  X(kCfiRomVerify,       0x5a7) \
  X(kCfiRomTryBoot,      0x235) \
  X(kCfiRomPreBootCheck, 0x43a) \
  X(kCfiRomBoot,         0x2e2)
// clang-format on

// Define counters and constant values required by the CFI counter macros.
CFI_DEFINE_COUNTERS(rom_counters, ROM_CFI_FUNC_COUNTERS_TABLE);

// Life cycle state of the chip.
lifecycle_state_t lc_state = (lifecycle_state_t)0;
// Boot data from flash.
boot_data_t boot_data = {0};
// Whether we are "simply" waking from low power mode.
static hardened_bool_t waking_from_low_power = 0;
// First stage (ROM-->ROM_EXT) secure boot keys loaded from OTP.
static sigverify_otp_key_ctx_t sigverify_ctx;
// A ram copy of the OTP word controlling how to handle flash ECC errors.
uint32_t flash_ecc_exc_handler_en;

/**
 * Prints a status message indicating that the ROM is entering bootstrap mode.
 */
static void rom_bootstrap_message(void) {
  uart_putchar('b');
  uart_putchar('o');
  uart_putchar('o');
  uart_putchar('t');
  uart_putchar('s');
  uart_putchar('t');
  uart_putchar('r');
  uart_putchar('a');
  uart_putchar('p');
  uart_putchar(':');
  uart_putchar('1');
  uart_putchar('\r');
  uart_putchar('\n');
}

/**
 * Performs once-per-boot initialization of ROM modules and peripherals.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t rom_init(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomInit, 1);
  sec_mmio_init();
  uint32_t reset_reasons = rstmgr_reason_get();
  if (reset_reasons != (1U << RSTMGR_RESET_INFO_LOW_POWER_EXIT_BIT)) {
    // The above compares all bits, rather than just the one indication "low
    // power exit", because if there is any other reset reason, besides
    // LOW_POWER_EXIT, it means that the chip did full reset while coming out of
    // low power.  In that case, the state of AON IP blocks would have been
    // reset, and the ROM should not treat this as "waking from low power".
    waking_from_low_power = kHardenedBoolFalse;

    // Initialize pinmux configuration so we can use the UART, (except if waking
    // up from low power, as the pinmux will in such case have retained its
    // previous configuration.)
    pinmux_init();
  } else {
    waking_from_low_power = kHardenedBoolTrue;
  }

  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  // Set static_critical region format version.
  static_critical_version = kStaticCriticalVersion2;

  // There are no conditional checks before writing to this CSR because it is
  // expected that if relevant Ibex countermeasures are disabled, this will
  // result in a nop.
  CSR_WRITE(CSR_REG_SECURESEED, rnd_uint32());

  // Write the OTP value to bits 0 to 5 of the cpuctrl CSR.
  uint32_t cpuctrl_csr;
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  cpuctrl_csr = bitfield_field32_write(
      cpuctrl_csr, (bitfield_field32_t){.mask = 0x3f, .index = 0},
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET));
  CSR_WRITE(CSR_REG_CPUCTRL, cpuctrl_csr);

  lc_state = lifecycle_state_get();

  // Update epmp config for debug rom according to lifecycle state.
  rom_epmp_config_debug_rom(lc_state);

  if (launder32(waking_from_low_power) != kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(waking_from_low_power, kHardenedBoolFalse);
    // Re-initialize the watchdog timer, if the RESET was caused by anything
    // besides waking from low power (which would have left the watchdog in its
    // previous configuration).
    watchdog_init(lc_state);
    SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioInit);
  }

  // Initialize the shutdown policy.
  HARDENED_RETURN_IF_ERROR(shutdown_init(lc_state));

  flash_ctrl_init();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioInit);
  flash_ecc_exc_handler_en = otp_read32(
      OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_FLASH_ECC_EXC_HANDLER_EN_OFFSET);

  // Initialize in-memory copy of the ePMP register configuration.
  rom_epmp_state_init(lc_state);

  // Check that AST is in the expected state.
  HARDENED_RETURN_IF_ERROR(ast_check(lc_state));

  // Initialize the retention RAM based on the reset reason and the OTP value.
  // Note: Retention RAM is always reset on PoR regardless of the OTP value.
  uint32_t reset_mask =
      (1 << kRstmgrReasonPowerOn) |
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_RET_RAM_RESET_MASK_OFFSET);
  if ((reset_reasons & reset_mask) != 0) {
    retention_sram_init();
    retention_sram_get()->creator.last_shutdown_reason = kErrorOk;
  }

  // Initialize boot_log
  boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
  memset(boot_log, 0, sizeof(*boot_log));
  boot_log->identifier = kBootLogIdentifier;
  boot_log->chip_version = kChipInfo.scm_revision;
  boot_log->retention_ram_initialized =
      reset_reasons & reset_mask ? kHardenedBoolTrue : kHardenedBoolFalse;

  // Always store the retention RAM version so the ROM_EXT can depend on its
  // accuracy even after scrambling.
  retention_sram_get()->version = kRetentionSramVersion4;

  // Store the reset reason in retention RAM and clear the register.
  retention_sram_get()->creator.reset_reasons = reset_reasons;
  rstmgr_reason_clear(reset_reasons);

  // This function is a NOP unless ROM is built for an fpga.
  device_fpga_version_print();

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
OT_WARN_UNUSED_RESULT
static rom_error_t rom_verify(const manifest_t *manifest,
                              uint32_t *flash_exec) {
  // Check security version and manifest constraints.
  //
  // The poisoning work (`anti_rollback`) invalidates signatures if the
  // security version of the manifest is smaller than the minimum required
  // security version.
  const uint32_t extra_word = UINT32_MAX;
  const uint32_t *anti_rollback = NULL;
  size_t anti_rollback_len = 0;
  if (launder32(manifest->security_version) <
      boot_data.min_security_version_rom_ext) {
    anti_rollback = &extra_word;
    anti_rollback_len = sizeof(extra_word);
  }
  *flash_exec = 0;
  HARDENED_RETURN_IF_ERROR(boot_policy_manifest_check(manifest, &boot_data));

  // Load OTBN boot services app.
  //
  // This will be reused by later boot stages.
  HARDENED_RETURN_IF_ERROR(otbn_boot_app_load());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 1);

  // Load secure boot keys from OTP into RAM.
  HARDENED_RETURN_IF_ERROR(sigverify_otp_keys_init(&sigverify_ctx));
  // ECDSA key.
  const ecdsa_p256_public_key_t *ecdsa_key = NULL;
  HARDENED_RETURN_IF_ERROR(sigverify_ecdsa_p256_key_get(
      &sigverify_ctx,
      sigverify_ecdsa_p256_key_id_get(&manifest->ecdsa_public_key), lc_state,
      &ecdsa_key));
  // SPX+ key.
  const sigverify_spx_key_t *spx_key = NULL;
  const sigverify_spx_signature_t *spx_signature = NULL;
  uint32_t sigverify_spx_en = sigverify_spx_verify_enabled(lc_state);
  if (launder32(sigverify_spx_en) != kSigverifySpxDisabledOtp) {
    const manifest_ext_spx_key_t *ext_spx_key;
    HARDENED_RETURN_IF_ERROR(manifest_ext_get_spx_key(manifest, &ext_spx_key));
    HARDENED_RETURN_IF_ERROR(sigverify_spx_key_get(
        &sigverify_ctx, sigverify_spx_key_id_get(&ext_spx_key->key), lc_state,
        &spx_key));
    const manifest_ext_spx_signature_t *ext_spx_signature;
    HARDENED_RETURN_IF_ERROR(
        manifest_ext_get_spx_signature(manifest, &ext_spx_signature));
    spx_signature = &ext_spx_signature->signature;
  } else {
    HARDENED_CHECK_EQ(sigverify_spx_en, kSigverifySpxDisabledOtp);
  }

  // Measure ROM_EXT and portions of manifest via SHA256 digest.
  // Initialize ROM_EXT measurement in .static_critical with garbage.
  memset(boot_measurements.rom_ext.data, (int)rnd_uint32(),
         sizeof(boot_measurements.rom_ext.data));
  // Add anti-rollback poisoning word to measurement.
  hmac_sha256_init();
  hmac_sha256_update(anti_rollback, anti_rollback_len);
  HARDENED_CHECK_GE(manifest->security_version,
                    boot_data.min_security_version_rom_ext);
  // Add manifest usage constraints to the measurement.
  manifest_usage_constraints_t usage_constraints_from_hw;
  sigverify_usage_constraints_get(manifest->usage_constraints.selector_bits,
                                  &usage_constraints_from_hw);
  hmac_sha256_update(&usage_constraints_from_hw,
                     sizeof(usage_constraints_from_hw));
  // Add remaining part of manifest / ROM_EXT image to the measurement.
  manifest_digest_region_t digest_region = manifest_digest_region_get(manifest);
  // Add remaining part of manifest / ROM_EXT image to the measurement.
  hmac_sha256_update(digest_region.start, digest_region.length);
  hmac_digest_t act_digest;
  hmac_sha256_final(&act_digest);
  // Copy the ROM_EXT measurement to the .static_critical section.
  static_assert(sizeof(boot_measurements.rom_ext) == sizeof(act_digest),
                "Unexpected ROM_EXT digest size.");
  memcpy(&boot_measurements.rom_ext, &act_digest,
         sizeof(boot_measurements.rom_ext));

  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 2);

  /**
   * Verify the ECDSA/SPX+ signatures of ROM_EXT.
   *
   * We swap the order of signature verifications randomly.
   */
  *flash_exec = 0;
  if (rnd_uint32() < 0x80000000) {
    HARDENED_RETURN_IF_ERROR(sigverify_ecdsa_p256_verify(
        &manifest->ecdsa_signature, ecdsa_key, &act_digest, flash_exec));

    return sigverify_spx_verify(
        spx_signature, spx_key, lc_state, &usage_constraints_from_hw,
        sizeof(usage_constraints_from_hw), anti_rollback, anti_rollback_len,
        digest_region.start, digest_region.length, flash_exec);
  } else {
    HARDENED_RETURN_IF_ERROR(sigverify_spx_verify(
        spx_signature, spx_key, lc_state, &usage_constraints_from_hw,
        sizeof(usage_constraints_from_hw), anti_rollback, anti_rollback_len,
        digest_region.start, digest_region.length, flash_exec));

    return sigverify_ecdsa_p256_verify(&manifest->ecdsa_signature, ecdsa_key,
                                       &act_digest, flash_exec);
  }
}

/* These symbols are defined in
 * `opentitan/sw/device/silicon_creator/rom/rom.ld`, and describes the
 * location of the flash header.
 */
extern char _rom_ext_virtual_start_address[];
extern char _rom_ext_virtual_size[];
/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param manifest Pointer to the current manifest.
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
OT_WARN_UNUSED_RESULT
static inline uintptr_t rom_ext_vma_get(const manifest_t *manifest,
                                        uintptr_t lma_addr) {
  return (lma_addr - (uintptr_t)manifest +
          (uintptr_t)_rom_ext_virtual_start_address);
}

/**
 * Performs consistency checks before booting a ROM_EXT.
 *
 * All of the checks in this function are expected to pass and any failures
 * result in shutdown.
 */
static void rom_pre_boot_check(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 1);

  // Check the alert_handler configuration.
  SHUTDOWN_IF_ERROR(alert_config_check(lc_state));
  SHUTDOWN_IF_ERROR(rnd_health_config_check(lc_state));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 2);

  // Check cached life cycle state against the value reported by hardware.
  lifecycle_state_t lc_state_check = lifecycle_state_get();
  if (launder32(lc_state_check) != lc_state) {
    HARDENED_TRAP();
  }
  HARDENED_CHECK_EQ(lc_state_check, lc_state);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 3);

  // Check cached boot data.
  rom_error_t boot_data_ok = boot_data_check(&boot_data);
  if (launder32(boot_data_ok) != kErrorOk) {
    HARDENED_TRAP();
  }
  HARDENED_CHECK_EQ(boot_data_ok, kErrorOk);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 4);

  // Check the ePMP state
  SHUTDOWN_IF_ERROR(epmp_state_check());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 5);

  // Check the cpuctrl CSR.
  uint32_t cpuctrl_csr;
  uint32_t cpuctrl_otp =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_CPUCTRL_OFFSET);
  CSR_READ(CSR_REG_CPUCTRL, &cpuctrl_csr);
  // We only mask the 8th bit (`ic_scr_key_valid`) to include exception flags
  // (bits 6 and 7) in the check.
  cpuctrl_csr = bitfield_bit32_write(cpuctrl_csr, 8, false);
  if (launder32(cpuctrl_csr) != cpuctrl_otp) {
    HARDENED_TRAP();
  }
  HARDENED_CHECK_EQ(cpuctrl_csr, cpuctrl_otp);
  // Check rstmgr alert and cpu info collection configuration.
  SHUTDOWN_IF_ERROR(
      rstmgr_info_en_check(retention_sram_get()->creator.reset_reasons));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 6);

  sec_mmio_check_counters(/*expected_check_count=*/3);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomPreBootCheck, 7);
}

/**
 * Measures the combination of software configuration OTP digests and the digest
 * of the secure boot keys.
 *
 * @param measurement Pointer to the measurement of the partitions.
 * @return rom_error_t Result of the operation.
 */
static rom_error_t rom_measure_otp_partitions(
    keymgr_binding_value_t *measurement) {
  memset(measurement, (int)rnd_uint32(), sizeof(keymgr_binding_value_t));
  // These is no need to harden these data copies as any poisoning of the OTP
  // measurements will result in the derivation of a different UDS identity
  // which will not be endorsed. Hence we save the cycles of using sec_mmio.
  hmac_sha256_init();
  static_assert(
      (OTP_CTRL_CREATOR_SW_CFG_DIGEST_CREATOR_SW_CFG_DIGEST_FIELD_WIDTH *
       OTP_CTRL_CREATOR_SW_CFG_DIGEST_MULTIREG_COUNT / 8) == sizeof(uint64_t),
      "CreatorSwCfg OTP partition digest no longer 64 bits.");
  static_assert(
      (OTP_CTRL_OWNER_SW_CFG_DIGEST_OWNER_SW_CFG_DIGEST_FIELD_WIDTH *
       OTP_CTRL_OWNER_SW_CFG_DIGEST_MULTIREG_COUNT / 8) == sizeof(uint64_t),
      "OwnerSwCfg OTP partition digest no longer 64 bits.");
  hmac_sha256_update(
      (unsigned char *)(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                        OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                        OTP_CTRL_CREATOR_SW_CFG_DIGEST_0_REG_OFFSET),
      sizeof(uint64_t));
  hmac_sha256_update(
      (unsigned char *)(TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR +
                        OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET +
                        OTP_CTRL_OWNER_SW_CFG_DIGEST_0_REG_OFFSET),
      sizeof(uint64_t));
  hmac_sha256_update(sigverify_ctx.keys.integrity_measurement.digest,
                     kHmacDigestNumBytes);
  hmac_digest_t otp_measurement;
  hmac_sha256_final(&otp_measurement);
  memcpy(measurement->data, otp_measurement.digest, kHmacDigestNumBytes);
  return kErrorOk;
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
OT_WARN_UNUSED_RESULT
static rom_error_t rom_boot(const manifest_t *manifest, uint32_t flash_exec) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 1);
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateReset));

  boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
  boot_log->rom_ext_slot =
      manifest == boot_policy_manifest_a_get() ? kBootSlotA : kBootSlotB;
  boot_log_digest_update(boot_log);

  keymgr_binding_value_t otp_measurement;
  const keymgr_binding_value_t *attestation_measurement =
      &manifest->binding_value;
  uint32_t use_otp_measurement =
      otp_read32(OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_KEYMGR_OTP_MEAS_EN_OFFSET);
  if (launder32(use_otp_measurement) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(use_otp_measurement, kHardenedBoolTrue);
    rom_measure_otp_partitions(&otp_measurement);
    attestation_measurement = &otp_measurement;
  } else {
    HARDENED_CHECK_NE(use_otp_measurement, kHardenedBoolTrue);
  }
  sc_keymgr_sw_binding_set(&manifest->binding_value, attestation_measurement);
  sc_keymgr_creator_max_ver_set(manifest->max_key_version);
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioCreatorMaxVerSet);

  sec_mmio_check_counters(/*expected_check_count=*/2);

  // Configure address translation, compute the epmp regions and the entry
  // point for the virtual address in case the address translation is enabled.
  // Otherwise, compute the epmp regions and the entry point for the load
  // address.
  epmp_region_t text_region = manifest_code_region_get(manifest);
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  switch (launder32(manifest->address_translation)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolTrue);
      ibex_addr_remap_0_set((uintptr_t)_rom_ext_virtual_start_address,
                            (uintptr_t)manifest, (size_t)_rom_ext_virtual_size);
      SEC_MMIO_WRITE_INCREMENT(kAddressTranslationSecMmioConfigure);

      // Unlock read-only for the whole rom_ext virtual memory.
      HARDENED_RETURN_IF_ERROR(epmp_state_check());
      rom_epmp_unlock_rom_ext_r(
          (epmp_region_t){.start = (uintptr_t)_rom_ext_virtual_start_address,
                          .end = (uintptr_t)_rom_ext_virtual_start_address +
                                 (uintptr_t)_rom_ext_virtual_size});

      // Move the ROM_EXT execution section from the load address to the virtual
      // address.
      text_region.start = rom_ext_vma_get(manifest, text_region.start);
      text_region.end = rom_ext_vma_get(manifest, text_region.end);
      entry_point = rom_ext_vma_get(manifest, entry_point);
      break;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolFalse);
      break;
    default:
      HARDENED_TRAP();
  }

  // Unlock execution of ROM_EXT executable code (text) sections.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  rom_epmp_unlock_rom_ext_rx(text_region);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomBoot, 2, kCfiRomPreBootCheck);
  rom_pre_boot_check();
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 4);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomPreBootCheck, 8);

  // Enable execution of code from flash if signature is verified.
  flash_ctrl_exec_set(flash_exec);
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioExecSet);

  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(/*expected_check_count=*/5);

  // Jump to ROM_EXT entry point.
  enum {
    /**
     * Expected value of the `kCfiRomTryBoot` counter when jumping to the first
     * ROM_EXT image.
     */
    kCfiRomTryBootManifest0Val = 3 * kCfiIncrement + kCfiRomTryBootVal0,
    /**
     * Expected value of the `kCfiRomTryBoot` counter when jumping to the second
     * ROM_EXT image.
     */
    kCfiRomTryBootManifest1Val = 10 * kCfiIncrement + kCfiRomTryBootVal0,
  };
  const manifest_t *manifest_check = NULL;
  switch (launder32(rom_counters[kCfiRomTryBoot])) {
    case kCfiRomTryBootManifest0Val:
      HARDENED_CHECK_EQ(rom_counters[kCfiRomTryBoot],
                        kCfiRomTryBootManifest0Val);
      manifest_check = boot_policy_manifests_get().ordered[0];
      break;
    case kCfiRomTryBootManifest1Val:
      HARDENED_CHECK_EQ(rom_counters[kCfiRomTryBoot],
                        kCfiRomTryBootManifest1Val);
      manifest_check = boot_policy_manifests_get().ordered[1];
      break;
    default:
      HARDENED_TRAP();
  }
  HARDENED_CHECK_EQ(manifest, manifest_check);

#if OT_BUILD_FOR_STATIC_ANALYZER
  assert(manifest_check != NULL);
#endif

  if (launder32(manifest_check->address_translation) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(manifest_check->address_translation, kHardenedBoolTrue);
    HARDENED_CHECK_EQ(rom_ext_vma_get(manifest_check,
                                      manifest_entry_point_get(manifest_check)),
                      entry_point);
  } else {
    HARDENED_CHECK_EQ(manifest_check->address_translation, kHardenedBoolFalse);
    HARDENED_CHECK_EQ(manifest_entry_point_get(manifest_check), entry_point);
  }
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomBoot, 5);
  ((rom_ext_entry_point *)entry_point)();

  return kErrorRomBootFailed;
}

/**
 * Attempts to boot ROM_EXTs in the order given by the boot policy module.
 *
 * @return Result of the last attempt.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t rom_try_boot(void) {
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 1);

  // Read boot data from flash
  HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, &boot_data));

  boot_policy_manifests_t manifests = boot_policy_manifests_get();
  uint32_t flash_exec = 0;

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 2, kCfiRomVerify);
  rom_error_t error = rom_verify(manifests.ordered[0], &flash_exec);
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 4);

  if (launder32(error) == kErrorOk) {
    HARDENED_CHECK_EQ(error, kErrorOk);
    CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomVerify, 3);
    CFI_FUNC_COUNTER_INIT(rom_counters, kCfiRomTryBoot);
    CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 1, kCfiRomBoot);
    HARDENED_RETURN_IF_ERROR(rom_boot(manifests.ordered[0], flash_exec));
    return kErrorRomBootFailed;
  }

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 5, kCfiRomVerify);
  HARDENED_RETURN_IF_ERROR(rom_verify(manifests.ordered[1], &flash_exec));
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomTryBoot, 7);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomVerify, 3);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomTryBoot, 8, kCfiRomBoot);
  HARDENED_RETURN_IF_ERROR(rom_boot(manifests.ordered[1], flash_exec));
  return kErrorRomBootFailed;
}

void rom_main(void) {
  CFI_FUNC_COUNTER_INIT(rom_counters, kCfiRomMain);

  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomMain, 1, kCfiRomInit);
  SHUTDOWN_IF_ERROR(rom_init());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomMain, 3);
  CFI_FUNC_COUNTER_CHECK(rom_counters, kCfiRomInit, 3);

  if (launder32(waking_from_low_power) != kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(waking_from_low_power, kHardenedBoolFalse);
    hardened_bool_t bootstrap_req = bootstrap_requested();
    if (launder32(bootstrap_req) == kHardenedBoolTrue) {
      HARDENED_CHECK_EQ(bootstrap_req, kHardenedBoolTrue);
      rom_bootstrap_message();
      watchdog_disable();
      shutdown_finalize(bootstrap());
    }
  }

  // `rom_try_boot` will not return unless there is an error.
  CFI_FUNC_COUNTER_PREPCALL(rom_counters, kCfiRomMain, 4, kCfiRomTryBoot);
  shutdown_finalize(rom_try_boot());
}
