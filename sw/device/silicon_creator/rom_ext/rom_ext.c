// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/imm_rom_ext/imm_rom_ext.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
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
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_unlock.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_verify.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom_ext/rescue.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"
#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include "flash_ctrl_regs.h"                          // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sram_ctrl_regs.h"                           // Generated.

// Declaration for the ROM_EXT manifest start address, populated by the linker
extern char _rom_ext_start_address[];
// Declaration for the chip_info structure stored in ROM.
extern const char _rom_chip_info_start[];

// Life cycle state of the chip.
lifecycle_state_t lc_state = kLcStateProd;

// Owner configuration details parsed from the onwer info pages.
owner_config_t owner_config;

// Owner application keys.
owner_application_keyring_t keyring;

// ePMP regions for important address spaces.
const epmp_region_t kRamRegion = {
    .start = TOP_EARLGREY_RAM_MAIN_BASE_ADDR,
    .end = TOP_EARLGREY_RAM_MAIN_BASE_ADDR + TOP_EARLGREY_RAM_MAIN_SIZE_BYTES,
};

const epmp_region_t kMmioRegion = {
    .start = TOP_EARLGREY_MMIO_BASE_ADDR,
    .end = TOP_EARLGREY_MMIO_BASE_ADDR + TOP_EARLGREY_MMIO_SIZE_BYTES,
};

const epmp_region_t kRvDmRegion = {
    .start = TOP_EARLGREY_RV_DM_MEM_BASE_ADDR,
    .end = TOP_EARLGREY_RV_DM_MEM_BASE_ADDR + TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES,
};

const epmp_region_t kFlashRegion = {
    .start = TOP_EARLGREY_EFLASH_BASE_ADDR,
    .end = TOP_EARLGREY_EFLASH_BASE_ADDR + TOP_EARLGREY_EFLASH_SIZE_BYTES,
};

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);

  // TODO(opentitan#22947): Remove this debug print prior to a formal release.
  uint32_t mepc, mtval;
  CSR_READ(CSR_REG_MEPC, &mepc);
  CSR_READ(CSR_REG_MTVAL, &mtval);
  dbg_printf("MCAUSE=%x MEPC=%x MTVAL=%x\r\n", mcause, mepc, mtval);

  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorRomExtInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorRomExtInterrupt + mcause;
}

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
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  // TODO: Verify ePMP expectations from ROM.

  // Conditionally patch AST and check that it is in the expected state.
  HARDENED_RETURN_IF_ERROR(ast_patch(lc_state));

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

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_verify(const manifest_t *manifest,
                                  const boot_data_t *boot_data) {
  RETURN_IF_ERROR(rom_ext_boot_policy_manifest_check(manifest, boot_data));
  size_t kindex = 0;
  RETURN_IF_ERROR(owner_keyring_find_key(
      &keyring, kOwnershipKeyAlgRsa,
      sigverify_rsa_key_id_get(&manifest->rsa_modulus), &kindex));

  dbg_printf("app_verify: key=%u alg=%C domain=%C\r\n", kindex,
             keyring.key[kindex]->key_alg, keyring.key[kindex]->key_domain);

  memset(boot_measurements.bl0.data, (int)rnd_uint32(),
         sizeof(boot_measurements.bl0.data));

  hmac_sha256_init();
  // Hash usage constraints.
  manifest_usage_constraints_t usage_constraints_from_hw;
  // TODO(cfrantz): Combine key's usage constraints with manifest's
  // usage_constraints.
  sigverify_usage_constraints_get(manifest->usage_constraints.selector_bits,
                                  &usage_constraints_from_hw);
  hmac_sha256_update(&usage_constraints_from_hw,
                     sizeof(usage_constraints_from_hw));
  // Hash the remaining part of the image.
  manifest_digest_region_t digest_region = manifest_digest_region_get(manifest);
  hmac_sha256_update(digest_region.start, digest_region.length);
  // TODO(#19596): add owner configuration block to measurement.
  // Verify signature
  hmac_sha256_process();
  hmac_digest_t act_digest;
  hmac_sha256_final(&act_digest);

  static_assert(sizeof(boot_measurements.bl0) == sizeof(act_digest),
                "Unexpected BL0 digest size.");
  memcpy(&boot_measurements.bl0, &act_digest, sizeof(boot_measurements.bl0));

  uint32_t flash_exec = 0;
  return sigverify_rsa_verify(&manifest->rsa_signature,
                              &keyring.key[kindex]->data.rsa, &act_digest,
                              lc_state, &flash_exec);
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
static rom_error_t rom_ext_boot(const manifest_t *manifest) {
  // Generate CDI_1 attestation keys and certificate.
  HARDENED_RETURN_IF_ERROR(
      dice_chain_attestation_owner(&boot_measurements.bl0, manifest));

  // Write the DICE certs to flash if they have been updated.
  HARDENED_RETURN_IF_ERROR(dice_chain_flush_flash());

  // Remove write and erase access to the certificate pages before handing over
  // execution to the owner firmware (owner firmware can still read).
  flash_ctrl_cert_info_page_owner_restrict(
      &kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageDiceCerts);

  // Disable access to silicon creator info pages, the OTP creator partition
  // and the OTP direct access interface until the next reset.
  flash_ctrl_creator_info_pages_lockdown();
  otp_creator_sw_cfg_lockdown();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioCreatorInfoPagesLockdown +
                           kOtpSecMmioCreatorSwCfgLockDown);

  // ePMP region 15 gives read/write access to RAM.
  epmp_set_napot(15, kRamRegion, kEpmpPermReadWrite);

  // Reconfigure the ePMP MMIO region to be NAPOT region 14, thus freeing
  // up an ePMP entry for use elsewhere.
  epmp_set_napot(14, kMmioRegion, kEpmpPermReadWrite);

  // ePMP region 13 allows RvDM access.
  if (lc_state == kLcStateProd || lc_state == kLcStateProdEnd) {
    // No RvDM access in Prod states, so we can clear the entry.
    epmp_clear(13);
  } else {
    epmp_set_napot(13, kRvDmRegion, kEpmpPermReadWriteExecute);
  }

  // ePMP region 12 gives read access to all of flash for both M and U modes.
  // The flash access was in ePMP region 5.  Clear it so it doesn't take
  // priority over 12.
  epmp_set_napot(12, kFlashRegion, kEpmpPermReadOnly);
  epmp_clear(5);

  // Move the ROM_EXT TOR region from entries 3/4/6 to 9/10/11.
  // If the ROM_EXT is located in the virtual window, the ROM will have
  // configured ePMP entry 6 as the read-only region over the entire
  // window.
  //
  // If not using the virtual window, we move the ROM_EXT TOR region to
  // ePMP entries 10/11.
  // If using the virtual window, we move the ROM_EXT read-only region to
  // ePMP entry 11 and move the TOR region to 9/10.
  uint32_t start, end, vwindow;
  CSR_READ(CSR_REG_PMPADDR3, &start);
  CSR_READ(CSR_REG_PMPADDR4, &end);
  CSR_READ(CSR_REG_PMPADDR6, &vwindow);
  uint8_t rxindex = 10;
  if (vwindow) {
    rxindex = 9;
    uint32_t size = 1 << bitfield_count_trailing_zeroes32(~vwindow);
    vwindow = (vwindow & ~(size - 1)) << 2;
    size <<= 3;

    epmp_set_napot(11, (epmp_region_t){.start = vwindow, .end = vwindow + size},
                   kEpmpPermReadOnly);
  }
  epmp_set_tor(rxindex, (epmp_region_t){.start = start << 2, .end = end << 2},
               kEpmpPermReadExecute);
  for (int8_t i = (int8_t)rxindex - 1; i >= 0; --i) {
    epmp_clear((uint8_t)i);
  }
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
      ibex_addr_remap_1_set((uintptr_t)_owner_virtual_start_address,
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
      // Normally we'd want to clear the ROM region since we aren't using it
      // anymore and since it isn't being used to encode access to the virtual
      // window.  However, for SiVal, we want to keep low entries locked to
      // prevent using low entries to override policy in higher entries.
      // epmp_clear_rom_region();
      break;
    default:
      HARDENED_TRAP();
  }

  // Allow execution of owner stage executable code (text) sections,
  // unlock the ROM_EXT code regions so the next stage can re-use those
  // entries and clear RLB to prevent further changes to locked ePMP regions.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  epmp_set_tor(2, text_region, kEpmpPermReadExecute);

  // Now that we're done reconfiguring the ePMP, we'll clear the RLB bit to
  // prevent any modification to locked entries.
  epmp_clear_rlb();
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Lock the address translation windows.
  ibex_addr_remap_lockdown(0);
  ibex_addr_remap_lockdown(1);

  dbg_print_epmp();

  // Verify expectations before jumping to owner code.
  // TODO: we really want to call rnd_uint32 here to select a random starting
  // location for checking expectations.  However, rnd_uint32 read from OTP
  // to know if it's allowed to used the CSRNG and OTP is locked down.
  sec_mmio_check_values_except_otp(/*rnd_uint32()*/ 0,
                                   TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  // Jump to OWNER entry point.
  dbg_printf("entry: 0x%x\r\n", (unsigned int)entry_point);
  ((owner_stage_entry_point *)entry_point)();

  return kErrorRomExtBootFailed;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_next_boot_bl0_slot_handler(
    boot_svc_msg_t *boot_svc_msg, boot_data_t *boot_data) {
  uint32_t active_slot = boot_data->primary_bl0_slot;
  uint32_t primary_slot = boot_svc_msg->next_boot_bl0_slot_req.primary_bl0_slot;
  rom_error_t error = kErrorOk;

  // If the requested primary slot is the same as the active slot, this request
  // is a no-op.
  if (active_slot != primary_slot) {
    switch (primary_slot) {
      case kBootSlotA:
      case kBootSlotB:
        boot_data->primary_bl0_slot = primary_slot;
        // Write boot data, updating relevant fields and recomputing the digest.
        HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
        // Read the boot data back to ensure the correct slot is booted this
        // time.
        HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));
        break;
      case kBootSlotUnspecified:
        // Do nothing.
        break;
      default:
        error = kErrorBootSvcBadSlot;
    }
  }

  // Record the new primary slot for use in the response message.
  active_slot = boot_data->primary_bl0_slot;

  uint32_t next_slot = boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;
  switch (launder32(next_slot)) {
    case kBootSlotA:
    case kBootSlotB:
      // We overwrite the RAM copy of the primary slot to the requested next
      // slot. This will cause a one-time boot of the requested side.
      boot_data->primary_bl0_slot = next_slot;
      break;
    case kBootSlotUnspecified:
      // Do nothing.
      break;
    default:
      error = kErrorBootSvcBadSlot;
  }

  boot_svc_next_boot_bl0_slot_res_init(error, active_slot,
                                       &boot_svc_msg->next_boot_bl0_slot_res);
  // We always return OK here because we've logged any error status in the boot
  // services response message and we want the boot flow to continue.
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_min_sec_ver_handler(boot_svc_msg_t *boot_svc_msg,
                                                boot_data_t *boot_data) {
  const uint32_t current_min_sec_ver = boot_data->min_security_version_bl0;
  const uint32_t requested_min_sec_ver =
      boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;

  // Ensure the requested minimum security version isn't lower than the current
  // minimum security version.
  if (launder32(requested_min_sec_ver) > current_min_sec_ver) {
    HARDENED_CHECK_GT(requested_min_sec_ver, current_min_sec_ver);
    uint32_t max_sec_ver = current_min_sec_ver;

    // Check the two flash slots for valid manifests and determine the maximum
    // value of the new minimum_security_version.  This prevents a malicious
    // MinBl0SecVer request from making the chip un-bootable.
    const manifest_t *manifest = rom_ext_boot_policy_manifest_a_get();
    rom_error_t error = rom_ext_verify(manifest, boot_data);
    if (error == kErrorOk && manifest->security_version > max_sec_ver) {
      max_sec_ver = manifest->security_version;
    }
    manifest = rom_ext_boot_policy_manifest_b_get();
    error = rom_ext_verify(manifest, boot_data);
    if (error == kErrorOk && manifest->security_version > max_sec_ver) {
      max_sec_ver = manifest->security_version;
    }

    if (requested_min_sec_ver <= max_sec_ver) {
      HARDENED_CHECK_LE(requested_min_sec_ver, max_sec_ver);
      // Update boot data to the requested minimum BL0 security version.
      boot_data->min_security_version_bl0 = requested_min_sec_ver;

      // Write boot data, updating relevant fields and recomputing the digest.
      HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
      // Read the boot data back to ensure the correct policy is used this boot.
      HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));

      boot_svc_min_bl0_sec_ver_res_init(boot_data->min_security_version_bl0,
                                        kErrorOk,
                                        &boot_svc_msg->min_bl0_sec_ver_res);

      HARDENED_CHECK_EQ(requested_min_sec_ver,
                        boot_data->min_security_version_bl0);
      return kErrorOk;
    }
  }
  boot_svc_min_bl0_sec_ver_res_init(current_min_sec_ver, kErrorBootSvcBadSecVer,
                                    &boot_svc_msg->min_bl0_sec_ver_res);
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t handle_boot_svc(boot_data_t *boot_data) {
  boot_svc_msg_t *boot_svc_msg = &retention_sram_get()->creator.boot_svc_msg;
  // TODO(lowRISC#22387): Examine the boot_svc code paths for boot loops.
  if (boot_svc_msg->header.identifier == kBootSvcIdentifier) {
    HARDENED_RETURN_IF_ERROR(boot_svc_header_check(&boot_svc_msg->header));
    uint32_t msg_type = boot_svc_msg->header.type;
    switch (launder32(msg_type)) {
      case kBootSvcEmptyReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcEmptyReqType);
        boot_svc_empty_res_init(&boot_svc_msg->empty);
        break;
      case kBootSvcNextBl0SlotReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcNextBl0SlotReqType);
        return boot_svc_next_boot_bl0_slot_handler(boot_svc_msg, boot_data);
      case kBootSvcMinBl0SecVerReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcMinBl0SecVerReqType);
        return boot_svc_min_sec_ver_handler(boot_svc_msg, boot_data);
      case kBootSvcOwnershipUnlockReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcOwnershipUnlockReqType);
        return ownership_unlock_handler(boot_svc_msg, boot_data);
      case kBootSvcOwnershipActivateReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcOwnershipActivateReqType);
        return ownership_activate_handler(boot_svc_msg, boot_data);
      case kBootSvcEmptyResType:
      case kBootSvcNextBl0SlotResType:
      case kBootSvcMinBl0SecVerResType:
      case kBootSvcOwnershipUnlockResType:
      case kBootSvcOwnershipActivateResType:
        // For response messages left in ret-ram we do nothing.
        break;
      default:
          // For messages with an unknown msg_type, we do nothing.
          ;
    }
  }
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_try_next_stage(boot_data_t *boot_data,
                                          boot_log_t *boot_log) {
  rom_ext_boot_policy_manifests_t manifests =
      rom_ext_boot_policy_manifests_get(boot_data);
  rom_error_t error = kErrorRomExtBootFailed;
  rom_error_t slot[2] = {0, 0};
  for (size_t i = 0; i < ARRAYSIZE(manifests.ordered); ++i) {
    error = rom_ext_verify(manifests.ordered[i], boot_data);
    slot[i] = error;
    if (error != kErrorOk) {
      continue;
    }

    if (manifests.ordered[i] == rom_ext_boot_policy_manifest_a_get()) {
      boot_log->bl0_slot = kBootSlotA;
    } else if (manifests.ordered[i] == rom_ext_boot_policy_manifest_b_get()) {
      boot_log->bl0_slot = kBootSlotB;
    } else {
      return kErrorRomExtBootFailed;
    }
    boot_log_digest_update(boot_log);

    // Boot fails if a verified ROM_EXT cannot be booted.
    RETURN_IF_ERROR(rom_ext_boot(manifests.ordered[i]));
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

static rom_error_t rom_ext_start(boot_data_t *boot_data, boot_log_t *boot_log) {
  HARDENED_RETURN_IF_ERROR(rom_ext_init(boot_data));
  const manifest_t *self = rom_ext_manifest();
  dbg_printf("Starting ROM_EXT %u.%u\r\n", self->version_major,
             self->version_minor);

  // Prepare dice chain builder for CDI_1.
  HARDENED_RETURN_IF_ERROR(dice_chain_init());

  // Initialize the boot_log in retention RAM.
  const chip_info_t *rom_chip_info = (const chip_info_t *)_rom_chip_info_start;
  boot_log_check_or_init(boot_log, rom_ext_current_slot(), rom_chip_info);
  boot_log->rom_ext_major = self->version_major;
  boot_log->rom_ext_minor = self->version_minor;
  boot_log->rom_ext_size = CHIP_ROM_EXT_SIZE_MAX;
  boot_log->rom_ext_nonce = boot_data->nonce;
  boot_log->ownership_state = boot_data->ownership_state;
  boot_log->ownership_transfers = boot_data->ownership_transfers;
  boot_log->rom_ext_min_sec_ver = boot_data->min_security_version_rom_ext;
  boot_log->bl0_min_sec_ver = boot_data->min_security_version_bl0;
  boot_log->primary_bl0_slot = boot_data->primary_bl0_slot;

  // Initialize the chip ownership state.
  rom_error_t error;
  error = ownership_init(boot_data, &owner_config, &keyring);
  if (error == kErrorWriteBootdataThenReboot) {
    return error;
  }
  // Configure SRAM execution as the owner requested.
  rom_ext_sram_exec(owner_config.sram_exec);

  // Handle any pending boot_svc commands.
  uint32_t reset_reasons = retention_sram_get()->creator.reset_reasons;
  uint32_t skip_boot_svc = reset_reasons & (1 << kRstmgrReasonLowPowerExit);
  if (skip_boot_svc == 0) {
    error = handle_boot_svc(boot_data);
    if (error == kErrorWriteBootdataThenReboot) {
      // Boot services reports errors by writing a status code into the reply
      // messages.  Regardless of whether a boot service request produced an
      // error, we want to continue booting unless the error specifically asks
      // for a reboot.
      return error;
    }
  }

  // Re-sync the boot_log entries that could be changed by boot services.
  boot_log->rom_ext_nonce = boot_data->nonce;
  boot_log->ownership_state = boot_data->ownership_state;
  boot_log_digest_update(boot_log);

  if (uart_break_detect(kRescueDetectTime) == kHardenedBoolTrue) {
    dbg_printf("rescue: remember to clear break\r\n");
    uart_enable_receiver();
    // TODO: update rescue protocol to accept boot data and rescue
    // config from the owner_config.
    error = rescue_protocol(boot_data, owner_config.rescue);
  } else {
    error = rom_ext_try_next_stage(boot_data, boot_log);
  }
  return error;
}

void rom_ext_main(void) {
  // TODO(opentitan#24368): Call immutable main in .rom_ext_immutable.
  // The immutable rom_ext startup code is not ready yet, so we call it here
  // to avoid breaking tests.
  imm_rom_ext_main();

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

void rom_ext_interrupt_handler(void) { shutdown_finalize(rom_ext_irq_error()); }

// We only need a single handler for all ROM_EXT interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the ROM_EXT,
// alias all interrupt handler symbols to the single handler.
OT_ALIAS("rom_ext_interrupt_handler")
void rom_ext_exception_handler(void);

OT_ALIAS("rom_ext_interrupt_handler")
void rom_ext_nmi_handler(void);

// A no-op immutable rom_ext fallback to avoid breaking tests before the
// proper bazel target is ready.
// TODO(opentitan#24368): Remove this nop fallback.
OT_SECTION(".rom_ext_immutable.fallback")
void imm_rom_ext_placeholder(void) {}
