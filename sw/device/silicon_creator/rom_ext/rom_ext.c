// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom_ext/rescue.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_epmp.h"
#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sram_ctrl_regs.h"

// Declaration for the ROM_EXT manifest start address, populated by the linker
extern char _rom_ext_start_address[];
// Declaration for the chip_info structure stored in ROM.
extern const char _chip_info_start[];

// Life cycle state of the chip.
lifecycle_state_t lc_state = kLcStateProd;

// ePMP regions for important address spaces.
const epmp_region_t kMmioRegion = {
    .start = TOP_EARLGREY_MMIO_BASE_ADDR,
    .end = TOP_EARLGREY_MMIO_BASE_ADDR + TOP_EARLGREY_MMIO_SIZE_BYTES,
};

const epmp_region_t kFlashRegion = {
    .start = TOP_EARLGREY_EFLASH_BASE_ADDR,
    .end = TOP_EARLGREY_EFLASH_BASE_ADDR + TOP_EARLGREY_EFLASH_SIZE_BYTES,
};

const epmp_region_t kAstRegion = {
    .start = TOP_EARLGREY_AST_BASE_ADDR,
    .end = TOP_EARLGREY_AST_BASE_ADDR + TOP_EARLGREY_AST_SIZE_BYTES,
};

const epmp_region_t kOtpRegion = {
    // We only want to lock out the register, not the memory mapped interface.
    // The size of the register space is 0x1000 bytes.
    .start = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR,
    .end = TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR + 0x1000,
};

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);
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
  uint32_t pc = 0;
  asm("auipc %[pc], 0;" : [pc] "=r"(pc));

  const uint32_t kFlashSlotA = TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
  const uint32_t kFlashSlotB =
      kFlashSlotA + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2;
  const uint32_t kFlashSlotEnd =
      kFlashSlotA + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES;
  if (pc >= kFlashSlotA && pc < kFlashSlotB) {
    // Running in Slot A.
    return kRomExtBootSlotA;
  } else if (pc >= kFlashSlotB && pc < kFlashSlotEnd) {
    // Running in Slot B.
    return kRomExtBootSlotB;
  } else {
    // Running elsewhere (ie: the remap window).
    // TODO: read the remap register configuration to determine the execution
    // slot.
    return kBootLogUninitialized;
  }
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
static rom_error_t rom_ext_init(void) {
  sec_mmio_next_stage_init();
  lc_state = lifecycle_state_get();
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  // TODO: Verify ePMP expectations from ROM.

  // Conditionally patch AST and check that it is in the expected state.
  HARDENED_RETURN_IF_ERROR(ast_patch(lc_state));

  // Check that the retention RAM is initialized.
  HARDENED_RETURN_IF_ERROR(retention_sram_check_version());

  return kErrorOk;
}

void rom_ext_sram_exec(hardened_bool_t enable) {
  switch (enable) {
    case kHardenedBoolTrue:
      // In the case where we enable SRAM exec, we do not lock the register as
      // some later code may want to disable it.
      HARDENED_CHECK_EQ(enable, kHardenedBoolTrue);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4True);
      break;
    case kHardenedBoolFalse:
      // In the case where we disable SRAM exec, we lock the register so that it
      // cannot be re-enabled later.
      HARDENED_CHECK_EQ(enable, kHardenedBoolFalse);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4False);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REGWEN_REG_OFFSET,
                       0);
      break;
    default:
      HARDENED_TRAP();
  }
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_verify(const manifest_t *manifest,
                                  const boot_data_t *boot_data) {
  RETURN_IF_ERROR(rom_ext_boot_policy_manifest_check(manifest, boot_data));
  const sigverify_rsa_key_t *key;
  RETURN_IF_ERROR(sigverify_rsa_key_get(
      sigverify_rsa_key_id_get(&manifest->rsa_modulus), &key));

  hmac_sha256_init();
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

  uint32_t flash_exec = 0;
  return sigverify_rsa_verify(&manifest->rsa_signature, key, &act_digest,
                              lc_state, &flash_exec);
}

/* These symbols are defined in
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
static rom_error_t rom_ext_attestation_keygen(const manifest_t *manifest) {
  attestation_public_key_t curr_attestation_pubkey = {.x = {0}, .y = {0}};

  // Initialize the entropy complex for key manager operations.
  // Note: `OTCRYPTO_OK.value` is equal to `kErrorOk` but we cannot add a static
  // assertion here since its definition is not an integer constant expression.
  HARDENED_RETURN_IF_ERROR((rom_error_t)entropy_complex_init().value);

  // Initialize KMAC for key manager operations.
  HARDENED_RETURN_IF_ERROR(kmac_keymgr_configure());

  // Load OTBN attestation keygen program.
  HARDENED_RETURN_IF_ERROR(otbn_boot_app_load());

  // ROM sets the SW binding values for the first key stage (CreatorRootKey) but
  // does not initialize the key manager. Advance key manager state twice to
  // transition to the creator root key state.
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateInit));
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateCreatorRootKey));

  // Generate UDS attestation keys.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kUdsAttestationKeySeed, kUdsKeymgrDiversifier, &curr_attestation_pubkey));
  // TODO(#19588): check UDS public key matches that in UDS cert.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kUdsAttestationKeySeed, kUdsKeymgrDiversifier));

  // Advance keymgr to OwnerIntermediate stage (root of Sealing_0 and CDI_0).
  sc_keymgr_sw_binding_unlock_wait();
  // We set the sealing binding value to all 0s, as sealing keys are not
  // currently used at the ROM_EXT stage. For the attestation binding value, we
  // use the ROM_EXT measurement preloaded in `static_critical` section by ROM.
  keymgr_binding_value_t zero_binding_value = {.data = {0}};
  sc_keymgr_sw_binding_set(
      /*binding_value_sealing=*/&zero_binding_value,
      /*binding_value_attestation=*/&boot_measurements.rom_ext);
  const manifest_t *rom_ext_manifest =
      (const manifest_t *)_rom_ext_start_address;
  sc_keymgr_owner_int_max_ver_set(rom_ext_manifest->max_key_version);
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerIntMaxVerSet);
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(
      sc_keymgr_state_check(kScKeymgrStateOwnerIntermediateKey));

  // Generate CDI_0 attestation keys.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kCdi0AttestationKeySeed, kCdi0KeymgrDiversifier,
      &curr_attestation_pubkey));
  // TODO(#19588): check ROM_EXT measurement / CDI_0 public key matches that in
  // CDI_0 cert. If not, update the cert and endorse it.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kCdi0AttestationKeySeed, kCdi0KeymgrDiversifier));

  // Advance keymgr to Owner stage (root of Sealing_1 and CDI_1).
  // TODO(ttrippel): Put the real BL0 measurement in here.
  sc_keymgr_sw_binding_unlock_wait();
  sc_keymgr_sw_binding_set(/*binding_value_sealing=*/&manifest->binding_value,
                           /*binding_value_attestation=*/&zero_binding_value);
  sc_keymgr_owner_max_ver_set(manifest->max_key_version);
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerMaxVerSet);
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateOwnerKey));

  // Generate CDI_1 attestation keys.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_keygen(
      kCdi1AttestationKeySeed, kCdi1KeymgrDiversifier,
      &curr_attestation_pubkey));
  // TODO(#19588): check ROM_EXT measurement / CDI_1 public key matches that in
  // CDI_1 cert. If not, update the cert and endorse it.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kCdi1AttestationKeySeed, kCdi1KeymgrDiversifier));

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_boot(const manifest_t *manifest) {
  // Crank the keymgr and validate attestation certificates.
  HARDENED_RETURN_IF_ERROR(rom_ext_attestation_keygen(manifest));

  // Disable access to silicon creator info pages, the OTP creator partition
  // and the OTP direct access interface until the next reset.
  flash_ctrl_creator_info_pages_lockdown();
  otp_creator_sw_cfg_lockdown();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioCreatorInfoPagesLockdown +
                           kOtpSecMmioCreatorSwCfgLockDown);

  // ePMP region 15 gives access to RAM and is already configured correctly.

  // Reconfigure the ePMP MMIO region to be NAPOT region 14, thus freeing
  // up an ePMP entry for use elsewhere.
  rom_ext_epmp_set_napot(14, kMmioRegion, kEpmpPermLockedReadWrite);

  // ePMP region 13 allows RvDM access and is already configured correctly.

  // ePMP region 12 gives read access to all of flash for both M and U modes.
  // The flash access was in ePMP region 5.  Clear it so it doesn't take
  // priority over 12.
  rom_ext_epmp_set_napot(12, kFlashRegion, kEpmpPermLockedReadOnly);
  rom_ext_epmp_clear(5);

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

    rom_ext_epmp_set_napot(
        11, (epmp_region_t){.start = vwindow, .end = vwindow + size},
        kEpmpPermReadOnly);
  }
  rom_ext_epmp_set_tor(rxindex,
                       (epmp_region_t){.start = start << 2, .end = end << 2},
                       kEpmpPermReadExecute);
  for (int8_t i = (int8_t)rxindex - 1; i >= 0; --i) {
    rom_ext_epmp_clear((uint8_t)i);
  }

  // Use the ePMP to forbid access to the OTP DAI interface.
  // TODO(cfrantz): This lockout is for silicon validation testing.
  // We want to prevent accidental OTP programming by test programs before we
  // commit to a finalized OTP configuration on test chips.  Since the OTP
  // controller doesn't have a per-boot register lockout, we'll use the ePMP to
  // disable access to the programming interface.
  rom_ext_epmp_set_napot(0, kOtpRegion, kEpmpPermLockedNoAccess);

  // TODO(cfrantz): This lockout is for silicon validation testing.
  // We want to prevent access to the AST by test programs before we commit
  // to a finalized AST configuration set in OTP.
  rom_ext_epmp_set_napot(1, kAstRegion, kEpmpPermLockedNoAccess);
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
      rom_ext_epmp_set_napot(
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
      // rom_ext_epmp_clear_rom_region();
      break;
    default:
      HARDENED_TRAP();
  }

  // Allow execution of owner stage executable code (text) sections,
  // unlock the ROM_EXT code regions so the next stage can re-use those
  // entries and clear RLB to prevent further changes to locked ePMP regions.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  rom_ext_epmp_set_tor(2, text_region, kEpmpPermReadExecute);

  // Now that we're done reconfiguring the ePMP, we'll clear the RLB bit to
  // prevent any modification to locked entries.
  rom_ext_epmp_clear_rlb();
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Forbid code execution from SRAM.
  rom_ext_sram_exec(kHardenedBoolFalse);

  dbg_print_epmp();
  // Jump to OWNER entry point.
  dbg_printf("entry: 0x%x\r\n", (unsigned int)entry_point);
  ((owner_stage_entry_point *)entry_point)();

  return kErrorRomExtBootFailed;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_next_boot_bl0_slot_handler(
    boot_svc_msg_t *boot_svc_msg, boot_data_t *boot_data) {
  uint32_t msg_bl0_slot = boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;
  // We overwrite the RAM copy of the primary slot to the requested  next slot.
  // This will cause a one-time boot of the requested side.
  rom_error_t error = kErrorOk;
  switch (launder32(msg_bl0_slot)) {
    case kBootSvcNextBootBl0SlotA:
      HARDENED_CHECK_EQ(msg_bl0_slot, kBootSvcNextBootBl0SlotA);
      boot_data->primary_bl0_slot = kBootDataSlotA;
      break;
    case kBootSvcNextBootBl0SlotB:
      HARDENED_CHECK_EQ(msg_bl0_slot, kBootSvcNextBootBl0SlotB);
      boot_data->primary_bl0_slot = kBootDataSlotB;
      break;
    default:
      error = kErrorBootSvcBadSlot;
  }

  boot_svc_next_boot_bl0_slot_res_init(error,
                                       &boot_svc_msg->next_boot_bl0_slot_res);
  retention_sram_get()->creator.boot_svc_msg = *boot_svc_msg;
  // We always return OK here because we've logged any error status in the boot
  // services response message and we want the boot flow to continue.
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_primary_boot_bl0_slot_handler(
    boot_svc_msg_t *boot_svc_msg, boot_data_t *boot_data) {
  uint32_t active_slot = boot_data->primary_bl0_slot;
  uint32_t requested_slot = boot_svc_msg->primary_bl0_slot_req.primary_bl0_slot;

  // In cases where the primary is already set to the requested slot, this
  // function is a no-op.
  if (launder32(active_slot) != launder32(requested_slot)) {
    HARDENED_CHECK_NE(active_slot, requested_slot);
    switch (launder32(requested_slot)) {
      case kBootDataSlotA:
        HARDENED_CHECK_EQ(requested_slot, kBootDataSlotA);
        boot_data->primary_bl0_slot = requested_slot;
        break;
      case kBootDataSlotB:
        HARDENED_CHECK_EQ(requested_slot, kBootDataSlotB);
        boot_data->primary_bl0_slot = requested_slot;
        break;
      default:
        HARDENED_TRAP();
    }

    // Write boot data, updating relevant fields and recomputing the digest.
    HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
    // Read the boot data back to ensure the correct slot is booted this time.
    HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));
  } else {
    HARDENED_CHECK_EQ(active_slot, requested_slot);
  }

  boot_svc_primary_bl0_slot_res_init(boot_data->primary_bl0_slot, kErrorOk,
                                     &boot_svc_msg->primary_bl0_slot_res);

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_min_sec_ver_handler(boot_svc_msg_t *boot_svc_msg,
                                                boot_data_t *boot_data) {
  const uint32_t current_min_sec_ver = boot_data->min_security_version_bl0;
  const uint32_t requested_min_sec_ver =
      boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;
  const uint32_t diff = requested_min_sec_ver - current_min_sec_ver;

  // Ensure the requested minimum security version isn't lower than the current
  // minimum security version.
  if (launder32(requested_min_sec_ver) > current_min_sec_ver) {
    HARDENED_CHECK_GT(requested_min_sec_ver, current_min_sec_ver);
    HARDENED_CHECK_LT(diff, requested_min_sec_ver);

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
  } else {
    boot_svc_min_bl0_sec_ver_res_init(current_min_sec_ver, kErrorOk,
                                      &boot_svc_msg->min_bl0_sec_ver_res);
  }

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_try_boot(void) {
  boot_data_t boot_data;
  HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, &boot_data));

  boot_svc_msg_t boot_svc_msg = retention_sram_get()->creator.boot_svc_msg;
  if (boot_svc_msg.header.identifier == kBootSvcIdentifier) {
    HARDENED_RETURN_IF_ERROR(boot_svc_header_check(&boot_svc_msg.header));
    uint32_t msg_type = boot_svc_msg.header.type;
    switch (launder32(msg_type)) {
      case kBootSvcEmptyType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcEmptyType);
        break;
      case kBootSvcNextBl0SlotReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcNextBl0SlotReqType);
        HARDENED_RETURN_IF_ERROR(
            boot_svc_next_boot_bl0_slot_handler(&boot_svc_msg, &boot_data));
        break;
      case kBootSvcPrimaryBl0SlotReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcPrimaryBl0SlotReqType);
        HARDENED_RETURN_IF_ERROR(
            boot_svc_primary_boot_bl0_slot_handler(&boot_svc_msg, &boot_data));
        break;
      case kBootSvcMinBl0SecVerReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcMinBl0SecVerReqType);
        HARDENED_RETURN_IF_ERROR(
            boot_svc_min_sec_ver_handler(&boot_svc_msg, &boot_data));
        break;
      case kBootSvcNextBl0SlotResType:
        // For response messages left in ret-ram we do nothing.
        break;
      default:
        HARDENED_TRAP();
    }
  }

  rom_ext_boot_policy_manifests_t manifests =
      rom_ext_boot_policy_manifests_get(&boot_data);
  rom_error_t error = kErrorRomExtBootFailed;
  rom_error_t slot[2] = {0, 0};
  for (size_t i = 0; i < ARRAYSIZE(manifests.ordered); ++i) {
    error = rom_ext_verify(manifests.ordered[i], &boot_data);
    slot[i] = error;
    if (error != kErrorOk) {
      continue;
    }

    boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
    if (manifests.ordered[i] == rom_ext_boot_policy_manifest_a_get()) {
      boot_log->bl0_slot = kBl0BootSlotA;
    } else if (manifests.ordered[i] == rom_ext_boot_policy_manifest_b_get()) {
      boot_log->bl0_slot = kBl0BootSlotB;
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

void rom_ext_main(void) {
  rom_ext_check_rom_expectations();
  SHUTDOWN_IF_ERROR(rom_ext_init());
  dbg_printf("Starting ROM_EXT\r\n");

  boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
  const chip_info_t *rom_chip_info = (const chip_info_t *)_chip_info_start;
  boot_log_check_or_init(boot_log, rom_ext_current_slot(), rom_chip_info);

  rom_error_t error;
  if (uart_break_detect(kRescueDetectTime) == kHardenedBoolTrue) {
    dbg_printf("rescue: remember to clear break\r\n");
    uart_enable_receiver();
    error = rescue_protocol();
  } else {
    error = rom_ext_try_boot();
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
