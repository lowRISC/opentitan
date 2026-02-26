// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/epmp.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/ownership/isfb.h"
#include "sw/device/silicon_creator/lib/ownership/owner_verify.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_unlock.h"
#include "sw/device/silicon_creator/lib/rescue/rescue.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"
#include "sw/device/silicon_creator/rom_ext/imm_section/imm_section_version.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_services.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_verify.h"

#include "hw/top/flash_ctrl_regs.h"                   // Generated.
#include "hw/top/otp_ctrl_regs.h"                     // Generated.
#include "hw/top/sram_ctrl_regs.h"                    // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// Useful constants for flash sizes and ROM_EXT locations.
enum {
  kFlashBankSize = FLASH_CTRL_PARAM_REG_PAGES_PER_BANK,
  kFlashPageSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
  kFlashTotalSize = 2 * kFlashBankSize,

  kRomExtSizeInPages = CHIP_ROM_EXT_SIZE_MAX / kFlashPageSize,
  kRomExtAStart = 0 / kFlashPageSize,
  kRomExtAEnd = kRomExtAStart + kRomExtSizeInPages,
  kRomExtBStart = kFlashBankSize + kRomExtAStart,
  kRomExtBEnd = kRomExtBStart + kRomExtSizeInPages,
};

// Parameter to check the ECDSA and SPX signatures with.
enum {
  kSigverifySignExec = 0xa26a38f7,
};

// Declaration for the ROM_EXT manifest start address, populated by the linker
extern char _rom_ext_start_address[];
// Declaration for the chip_info structure stored in ROM.
extern const char _rom_chip_info_start[];
// Declaration for the imm_section end address, populated by the linker
extern char _rom_ext_immutable_end[];
// Declaration for the imm_section size, populated by the linker
extern char _rom_ext_immutable_size[];

// Life cycle state of the chip.
lifecycle_state_t lc_state;

// A ram copy of the OTP word controlling how to handle flash ECC errors.
uint32_t flash_ecc_exc_handler_en;

// Owner configuration details parsed from the onwer info pages.
owner_config_t owner_config;

// The number of strike words and product extensions parsed from the ISFB
// configuration. Used to implement redundancy in the ISFB checks.
uint32_t isfb_check_count;

// Owner application keys.
owner_application_keyring_t keyring;

// Hash chain of all previous owners.
hmac_digest_t owner_history_hash;

// Verifying key index
size_t verify_key;

OT_WARN_UNUSED_RESULT
static uint32_t rom_ext_current_slot(void) {
  uint32_t pc = ibex_addr_remap_get(0);
  if (pc == 0) {
    // If the remap window has address zero, we're running from flash and we can
    // simply read the program counter.
    asm("auipc %[pc], 0;" : [pc] "=r"(pc));
  }

  const uint32_t kFlashSlotA = TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
  const uint32_t kFlashSlotB =
      kFlashSlotA + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2;
  const uint32_t kFlashSlotEnd =
      kFlashSlotA + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES;
  uint32_t side = 0;
  if (pc >= kFlashSlotA && pc < kFlashSlotB) {
    // Running in Slot A.
    side = kBootSlotA;
  } else if (pc >= kFlashSlotB && pc < kFlashSlotEnd) {
    // Running in Slot B.
    side = kBootSlotB;
  } else {
    // Not running in flash: impossible.
    HARDENED_TRAP();
  }
  return side;
}

void rom_ext_check_rom_expectations(void) {
  // Check the ePMP state.
  SHUTDOWN_IF_ERROR(epmp_state_check());
  // Check sec_mmio expectations.
  // We don't check the counters since we don't want to tie ROM_EXT to a
  // specific ROM version.
  sec_mmio_check_values(rnd_uint32());
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_init(boot_data_t *boot_data) {
  sec_mmio_next_stage_init();
  lc_state = lifecycle_state_get();
  flash_ecc_exc_handler_en = otp_read32(
      OTP_CTRL_PARAM_OWNER_SW_CFG_ROM_FLASH_ECC_EXC_HANDLER_EN_OFFSET);
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  // Reclaim entries 0 ~ 7 from ROM and ROM_EXT IMM_SECTION.
  for (int8_t i = 7; i >= 0; --i) {
    epmp_clear((uint8_t)i);
  }
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Check that the retention RAM is initialized.
  // TODO(lowrisc#22387): Check if return-if-error here is a potential
  // boot-loop.
  HARDENED_RETURN_IF_ERROR(retention_sram_check_version());

  // Get the boot_data record
  HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));

  return kErrorOk;
}

void rom_ext_sram_exec(owner_sram_exec_mode_t mode) {
  switch (mode) {
    case kOwnerSramExecModeEnabled:
      // In enabled mode, we do not lock the register so owner code can disable
      // SRAM exec at some later time.
      HARDENED_CHECK_EQ(mode, kOwnerSramExecModeEnabled);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4True);
      break;
    case kOwnerSramExecModeDisabled:
      // In disabled mode, we do not lock the register so owner code can enable
      // SRAM exec at some later time.
      HARDENED_CHECK_EQ(mode, kOwnerSramExecModeDisabled);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4False);
      break;
    case kOwnerSramExecModeDisabledLocked:
    default:
      // In disabled locked mode, we lock the register so the mode cannot be
      // changed.
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4False);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REGWEN_REG_OFFSET,
                       0);
      break;
  }
}

/**
 * These symbols are defined in
 * `opentitan/sw/device/silicon_creator/rom_ext/rom_ext.ld`, and describe the
 * location of the flash header.
 */
extern char _owner_virtual_start_address[];
extern char _owner_virtual_size[];

/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param manifest Pointer to the current manifest.
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
OT_WARN_UNUSED_RESULT
static uintptr_t owner_vma_get(const manifest_t *manifest, uintptr_t lma_addr) {
  return (lma_addr - (uintptr_t)manifest +
          (uintptr_t)_owner_virtual_start_address + CHIP_ROM_EXT_SIZE_MAX);
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_boot(boot_data_t *boot_data, boot_log_t *boot_log,
                                const manifest_t *manifest,
                                uint32_t *flash_exec) {
  // Determine which owner block the key came from and measure that block.
  hmac_digest_t owner_measurement;
  const owner_application_key_t *key = keyring.key[verify_key];
  owner_block_measurement(owner_block_key_page(key), &owner_measurement);

  keymgr_binding_value_t sealing_binding;
  if (boot_data->ownership_state == kOwnershipStateLockedOwner) {
    HARDENED_CHECK_EQ(boot_data->ownership_state, kOwnershipStateLockedOwner);
    // If we're in LockedOwner, initialize the sealing binding with the
    // diversification constant associated with key applicaiton key that
    // validated the owner firmware payload.
    static_assert(
        sizeof(key->raw_diversifier) == sizeof(keymgr_binding_value_t),
        "Expect the keymgr binding value to be the same size as an application "
        "key diversifier");
    memcpy(&sealing_binding, key->raw_diversifier, sizeof(sealing_binding));
  } else {
    // If we're not in LockedOwner state, we don't want to derive any valid
    // sealing keys, so set the binding constant to a nonsense value.
    memset(&sealing_binding, 0x55, sizeof(sealing_binding));
  }

  // Generate CDI_1 attestation keys and certificate.
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_owner(
      manifest, &boot_measurements.bl0, &owner_measurement, &owner_history_hash,
      &sealing_binding, key->key_domain));

  // Write the DICE certs to flash if they have been updated.
  HARDENED_RETURN_IF_ERROR(dice_chain_flush_flash());

  // Remove write and erase access to the certificate pages before handing over
  // execution to the owner firmware (owner firmware can still read).
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageDiceCerts);

  // Disable access to silicon creator info pages, the OTP creator partition
  // and the OTP direct access interface until the next reset.
  flash_ctrl_creator_info_pages_lockdown();
  otp_creator_sw_cfg_lockdown();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioCreatorInfoPagesLockdown +
                           kOtpSecMmioCreatorSwCfgLockDown);

  epmp_clear_lock_bits();

  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Configure address translation, compute the epmp regions and the entry
  // point for the virtual address in case the address translation is enabled.
  // Otherwise, compute the epmp regions and the entry point for the load
  // address.
  //
  // We'll map the owner code TOR region as ePMP entries 2/3. If using address
  // translation, we'll configure ePMP entry 4 as the read-only region.
  epmp_region_t text_region = manifest_code_region_get(manifest);
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  switch (launder32(manifest->address_translation)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolTrue);
      ibex_addr_remap_set(1, (uintptr_t)_owner_virtual_start_address,
                          (uintptr_t)manifest, (size_t)_owner_virtual_size);
      SEC_MMIO_WRITE_INCREMENT(kAddressTranslationSecMmioConfigure);

      // Unlock read-only for the whole rom_ext virtual memory.
      HARDENED_RETURN_IF_ERROR(epmp_state_check());
      epmp_set_napot(
          4,
          (epmp_region_t){.start = (uintptr_t)_owner_virtual_start_address,
                          .end = (uintptr_t)_owner_virtual_start_address +
                                 (uintptr_t)_owner_virtual_size},
          kEpmpPermReadOnly);
      HARDENED_RETURN_IF_ERROR(epmp_state_check());

      // Move the ROM_EXT execution section from the load address to the virtual
      // address.
      // TODO(#13513): Harden these calculations.
      text_region.start = owner_vma_get(manifest, text_region.start);
      text_region.end = owner_vma_get(manifest, text_region.end);
      entry_point = owner_vma_get(manifest, entry_point);
      break;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolFalse);
      break;
    default:
      HARDENED_TRAP();
  }

  // Allow execution of owner stage executable code (text) sections.
  epmp_set_tor(2, text_region, kEpmpPermReadExecute);
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Lock the address translation windows.
  ibex_addr_remap_lockdown(0);
  ibex_addr_remap_lockdown(1);

  if (launder32((hardened_bool_t)owner_config.isfb) != kHardenedBoolFalse) {
    hardened_bool_t node_locked = manifest->usage_constraints.selector_bits
                                      ? kHardenedBoolTrue
                                      : kHardenedBoolFalse;

    const manifest_ext_isfb_erase_t *ext_isfb_erase;
    rom_error_t ext_error =
        manifest_ext_get_isfb_erase(manifest, &ext_isfb_erase);

    hardened_bool_t erase_en = kHardenedBoolFalse;
    HARDENED_RETURN_IF_ERROR(isfb_info_flash_erase_policy_get(
        &owner_config, keyring.key[verify_key]->key_domain, node_locked,
        (ext_error == kErrorOk) ? ext_isfb_erase : NULL, &erase_en));

    if (launder32(erase_en) == kHardenedBoolTrue) {
      HARDENED_RETURN_IF_ERROR(
          owner_block_info_isfb_erase_enable(boot_data, &owner_config));
      HARDENED_CHECK_EQ(erase_en, kHardenedBoolTrue);
    }

    // Redundant check to ensure that the ISFB check was performed earlier in
    // the boot process.
    const manifest_ext_isfb_t *ext_isfb;
    rom_error_t error = manifest_ext_get_isfb(manifest, &ext_isfb);
    if (error == kErrorOk) {
      HARDENED_CHECK_EQ(isfb_check_count, isfb_expected_count_get(ext_isfb));
    } else {
      HARDENED_CHECK_NE(error, kErrorOk);
    }
  }

  // Lock the flash according to the ownership configuration.
  HARDENED_RETURN_IF_ERROR(
      ownership_flash_lockdown(boot_data, boot_log, &owner_config));
  // Lock the ownership info pages.
  ownership_pages_lockdown(boot_data, /*rescue=*/kHardenedBoolFalse);

  dbg_print_epmp();

  // Verify expectations before jumping to owner code.
  // TODO: we really want to call rnd_uint32 here to select a random starting
  // location for checking expectations.  However, rnd_uint32 read from OTP
  // to know if it's allowed to used the CSRNG and OTP is locked down.
  sec_mmio_check_values_except_otp(/*rnd_uint32()*/ 0,
                                   TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);

  HARDENED_CHECK_EQ(*flash_exec, kSigverifySignExec);

  // Jump to OWNER entry point.
  dbg_printf("entry: 0x%x\r\n", (unsigned int)entry_point);
  ((owner_stage_entry_point *)entry_point)();

  return kErrorRomExtBootFailed;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_try_next_stage(boot_data_t *boot_data,
                                          boot_log_t *boot_log) {
  rom_ext_boot_policy_manifests_t manifests =
      rom_ext_boot_policy_manifests_get(boot_data);
  rom_error_t error = kErrorRomExtBootFailed;
  rom_error_t slot[2] = {0, 0};
  for (size_t i = 0; i < ARRAYSIZE(manifests.ordered); ++i) {
    uint32_t flash_exec = 0;
    error =
        rom_ext_verify(manifests.ordered[i], boot_data, &flash_exec, &keyring,
                       &verify_key, &owner_config, &isfb_check_count);
    slot[i] = error;
    if (error != kErrorOk) {
      continue;
    }
    HARDENED_CHECK_EQ(flash_exec, kSigverifySignExec);

    if (manifests.ordered[i] == rom_ext_boot_policy_manifest_a_get()) {
      boot_log->bl0_slot = kBootSlotA;
    } else if (manifests.ordered[i] == rom_ext_boot_policy_manifest_b_get()) {
      boot_log->bl0_slot = kBootSlotB;
    } else {
      return kErrorRomExtBootFailed;
    }
    boot_log_digest_update(boot_log);

    // Boot fails if a verified ROM_EXT cannot be booted.
    RETURN_IF_ERROR(
        rom_ext_boot(boot_data, boot_log, manifests.ordered[i], &flash_exec));
    // `rom_ext_boot()` should never return `kErrorOk`, but if it does
    // we must shut down the chip instead of trying the next ROM_EXT.
    return kErrorRomExtBootFailed;
  }

  // If we get here, the loop exited after trying both slots.
  // If we see kErrorBootPolicyBadIdentifier as the error, we probably have an
  // empty slot.  In that case, the "bad identifier" error is not helpful, so
  // maybe choose the error from the other slot.
  if (error == kErrorBootPolicyBadIdentifier && error == slot[1]) {
    // If the bad identifier error comes from the non-primary slot, prefer
    // the error from the primary slot.
    error = slot[0];
  }
  return error;
}

static void rom_ext_flash_protect_self(uint32_t rom_ext_slot) {
  flash_ctrl_cfg_t cfg = flash_ctrl_data_default_cfg_get();
  flash_ctrl_perms_t read = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  };
  flash_ctrl_perms_t write = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  };
  flash_ctrl_data_region_protect(0, kRomExtAStart, kRomExtSizeInPages,
                                 rom_ext_slot == kBootSlotA ? read : write, cfg,
                                 kHardenedBoolTrue);
  flash_ctrl_data_region_protect(1, kRomExtBStart, kRomExtSizeInPages,
                                 rom_ext_slot == kBootSlotB ? read : write, cfg,
                                 kHardenedBoolTrue);
}

static void rom_ext_rescue_lockdown(boot_data_t *boot_data) {
  // Forbid SRAM execution.
  rom_ext_sram_exec(kOwnerSramExecModeDisabledLocked);
  // Set the keymgr to disabled and clear all sideloaded keys.
  sc_keymgr_disable();
  // Lock out OTP.
  otp_creator_sw_cfg_lockdown();
  // Lock the ePMP so it cannot be changed.
  epmp_set_lock_bits();
  epmp_clear_rlb();
  // Disable access to creator-level INFO pages.
  flash_ctrl_creator_info_pages_lockdown();
  // Set the OWNER_CONFIG pages for rescue mode (page0=ro, page1=rw).
  ownership_pages_lockdown(boot_data, /*rescue=*/kHardenedBoolTrue);
  // Lock access to owner-level INFO pages.  During normal boot, this
  // is performed by `ownership_flash_lockdown`, but we can't call that
  // function when entering rescue because rescue needs the flash DATA
  // segments to be writable.  Rescue has no need to access the INFO
  // pages, so we want to lock them for safety.
  owner_block_info_lockdown(owner_config.info);
}

static rom_error_t rom_ext_advance_secver(boot_data_t *boot_data,
                                          const manifest_t *manifest) {
  const manifest_ext_secver_write_t *secver;
  rom_error_t error;
  error = manifest_ext_get_secver_write(manifest, &secver);
  if (error == kErrorOk) {
    if (secver->write == kHardenedBoolTrue &&
        manifest->security_version > boot_data->min_security_version_rom_ext) {
      // If our security version is greater than the minimum security version
      // advance the minimum version to our version.
      boot_data->min_security_version_rom_ext = manifest->security_version;
      return boot_data_write(boot_data);
    }
  }
  return kErrorOk;
}

static rom_error_t rom_ext_start(boot_data_t *boot_data, boot_log_t *boot_log) {
  HARDENED_RETURN_IF_ERROR(rom_ext_init(boot_data));
  const manifest_t *self = rom_ext_manifest();

  lifecycle_claim(kMultiBitBool8True);
  lifecycle_set_status(kLifecycleStatusWordRomExtVersion, self->version_minor);
  lifecycle_set_status(kLifecycleStatusWordRomExtSecVersion,
                       self->security_version);
  lifecycle_set_status(kLifecycleStatusWordOwnerVersion, 0);
  lifecycle_set_status(kLifecycleStatusWordDeviceStatus,
                       kLifecycleDeviceStatusRomExtStart);
  lifecycle_claim(kMultiBitBool8False);

  dbg_printf("ROM_EXT:%u.%u\r\n", self->version_major, self->version_minor);

  // Print the version of immutable section if exists.
  if ((size_t)_rom_ext_immutable_size > kImmVersionSize) {
    imm_section_version_t *version =
        (imm_section_version_t *)((char *)_rom_ext_immutable_end -
                                  kImmVersionSize);
    dbg_printf("IMM_SECTION:%u.%u-%x%c\r\n", version->major, version->minor,
               version->commit_hash, version->build_status);
  }

  uint32_t hash_enforcement =
      otp_read32(OTP_CTRL_PARAM_CREATOR_SW_CFG_IMMUTABLE_ROM_EXT_EN_OFFSET);
  if (hash_enforcement != kHardenedBoolTrue) {
    // CAUTION: The message below should match the message defined in:
    //   //sw/device/silicon_creator/rom_ext/imm_section/defs.bzl
    dbg_printf("info: imm_section hash unenforced\r\n");
  }

  // Maybe advance the security version.
  HARDENED_RETURN_IF_ERROR(rom_ext_advance_secver(boot_data, self));

  // Prepare dice chain builder for CDI_1.
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  HARDENED_RETURN_IF_ERROR(dice_chain_rom_ext_check());

  // Initialize the boot_log in retention RAM.
  const chip_info_t *rom_chip_info = (const chip_info_t *)_rom_chip_info_start;
  boot_log_check_or_init(boot_log, rom_ext_current_slot(), rom_chip_info);
  boot_log->rom_ext_major = self->version_major;
  boot_log->rom_ext_minor = self->version_minor;
  boot_log->rom_ext_size = CHIP_ROM_EXT_SIZE_MAX;
  // Even though `primary_bl0_slot` can be changed by boot svc, we initialize
  // it here so the "SetNextBl0" can do a one-time override of the RAM copy
  // of `boot_data`.
  boot_log->primary_bl0_slot = boot_data->primary_bl0_slot;

  // Protect the flash pages where the ROM_EXT is located.
  rom_ext_flash_protect_self(boot_log->rom_ext_slot);

  // Initialize the chip ownership state.
  rom_error_t error;
  error = ownership_init(boot_data, &owner_config, &keyring);
  if (error == kErrorWriteBootdataThenReboot) {
    return error;
  }
  // TODO(cfrantz): evaluate permissible ownership init failure conditions
  // and change this to HARDENED_RETURN_IF_ERROR.
  if (error != kErrorOk) {
    dbg_printf("error: ownership_init=%x\r\n", error);
  }

  // Configure SRAM execution as the owner requested.
  rom_ext_sram_exec(owner_config.sram_exec);

  // Get the ownership history.  We discard the error because there is no
  // meaningful action we could take in the event of an error.  If there
  // was an error, ownership_history_get will default history hash result to
  // all ones.
  OT_DISCARD(ownership_history_get(&owner_history_hash));

  // Handle any pending boot_svc commands.
  uint32_t reset_reasons = retention_sram_get()->creator.reset_reasons;
  hardened_bool_t waking_from_low_power =
      reset_reasons & (1 << kRstmgrReasonLowPowerExit) ? kHardenedBoolTrue
                                                       : kHardenedBoolFalse;

  // We don't want to execute boot_svc requests if this is a low-power wakeup.
  if (waking_from_low_power != kHardenedBoolTrue) {
    boot_svc_msg_t *boot_svc_msg = &retention_sram_get()->creator.boot_svc_msg;
    error =
        boot_svc_handler(boot_svc_msg, boot_data, boot_log, lc_state, &keyring,
                         &verify_key, &owner_config, &isfb_check_count);
    if (error == kErrorWriteBootdataThenReboot) {
      // Boot services reports errors by writing a status code into the reply
      // messages.  Regardless of whether a boot service request produced an
      // error, we want to continue booting unless the error specifically asks
      // for a reboot.
      return error;
    }
  }

  // Synchronize the boot_log entries that could be changed by boot services.
  boot_log->rom_ext_nonce = boot_data->nonce;
  boot_log->ownership_state = boot_data->ownership_state;
  boot_log->ownership_transfers = boot_data->ownership_transfers;
  boot_log->rom_ext_min_sec_ver = boot_data->min_security_version_rom_ext;
  boot_log->bl0_min_sec_ver = boot_data->min_security_version_bl0;
  boot_log_digest_update(boot_log);

  // Now that boot services is finished, the ownership sealing key is no longer
  // needed.
  HARDENED_RETURN_IF_ERROR(ownership_seal_clear());

  // We don't want to enter rescue mode if this is a low-power wakeup.
  hardened_bool_t want_rescue = waking_from_low_power != kHardenedBoolTrue
                                    ? rescue_detect_entry(owner_config.rescue)
                                    : kHardenedBoolFalse;
  hardened_bool_t boot_attempted = kHardenedBoolFalse;

  if (want_rescue == kHardenedBoolFalse) {
    // If rescue wasn't triggered, try booting the next stage.
    error = rom_ext_try_next_stage(boot_data, boot_log);
    boot_attempted = kHardenedBoolTrue;
  }

  // If we haven't already entered rescue and rescue is requested (either by
  // the rescue trigger or by a boot failure), then enter rescue.
  if (want_rescue == kHardenedBoolTrue ||
      rescue_enter_on_fail(owner_config.rescue) == kHardenedBoolTrue) {
    rom_ext_rescue_lockdown(boot_data);
    if (error != kErrorOk) {
      dbg_printf("BFV:%x\r\n", error);
    }

    // Disable the watchdog timer when entering rescue mode.
    watchdog_disable();
    error = rescue_protocol(boot_data, boot_log, owner_config.rescue);

    // If rescue timed out and we didn't attempt to boot, request skipping
    // rescue on the next boot.  This will permit booting owner code if
    // the rescue trigger is stuck for some reason.
    if (error == kErrorRescueInactivity &&
        boot_attempted == kHardenedBoolFalse) {
      rescue_skip_next_boot();
      rstmgr_reboot();
    }
  }

  return error;
}

void rom_ext_main(void) {
  rom_ext_check_rom_expectations();
  boot_data_t boot_data;
  boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;

  rom_error_t error = rom_ext_start(&boot_data, boot_log);
  if (error == kErrorWriteBootdataThenReboot) {
    HARDENED_CHECK_EQ(error, kErrorWriteBootdataThenReboot);
    error = boot_data_write(&boot_data);
  }
  shutdown_finalize(error);
}
