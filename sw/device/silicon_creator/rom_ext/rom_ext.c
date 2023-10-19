// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/rom_print.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom_ext/bootstrap.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_epmp.h"
#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.

// Life cycle state of the chip.
lifecycle_state_t lc_state = kLcStateProd;

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

void rom_ext_check_rom_expectations(void) {
  // Check the ePMP state.
  SHUTDOWN_IF_ERROR(epmp_state_check());
  // Check sec_mmio expectations.
  // We don't check the counters since we don't want to tie ROM_EXT to a
  // specific ROM version.
  sec_mmio_check_values(rnd_uint32());
}

void rom_ext_init(void) {
  sec_mmio_next_stage_init();

  lc_state = lifecycle_state_get();

  // TODO: Verify ePMP expectations from ROM.

  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_verify(const manifest_t *manifest,
                                  const boot_data_t *boot_data) {
  RETURN_IF_ERROR(rom_ext_boot_policy_manifest_check(manifest, boot_data));
  const sigverify_rsa_key_t *key;
  RETURN_IF_ERROR(sigverify_rsa_key_get(
      sigverify_rsa_key_id_get(&manifest->rsa_modulus), &key));
  memset(boot_measurements.bl0.data, (int)rnd_uint32(),
         sizeof(boot_measurements.bl0.data));

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
  static_assert(sizeof(boot_measurements.bl0) == sizeof(act_digest),
                "Unexpected BL0 digest size.");
  memcpy(&boot_measurements.bl0, &act_digest, sizeof(boot_measurements.bl0));

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
static rom_error_t rom_ext_boot(const manifest_t *manifest) {
  // Initialize the entropy complex for key manager operations.
  // Note: `OTCRYPTO_OK.value` is equal to `kErrorOk` but we cannot add a static
  // assertion here since its definition is not an integer constant expression.
  HARDENED_RETURN_IF_ERROR((rom_error_t)entropy_complex_init().value);
  // ROM sets the SW binding values but does not initialize the key manager.
  // Advance key manager state twice to transition to the creator root key
  // state.
  keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(keymgr_state_check(kKeymgrStateInit));
  keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(keymgr_state_check(kKeymgrStateCreatorRootKey));
  // Set binding and max version for BL0.
  keymgr_sw_binding_unlock_wait();
  keymgr_sw_binding_set(&manifest->binding_value, &boot_measurements.bl0);
  keymgr_owner_int_max_ver_set(manifest->max_key_version);
  SEC_MMIO_WRITE_INCREMENT(kKeymgrSecMmioSwBindingSet +
                           kKeymgrSecMmioOwnerIntMaxVerSet);
  // Transition to the owner intermediate key state.
  keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(
      keymgr_state_check(kKeymgrStateOwnerIntermediateKey));
  keymgr_sw_binding_unlock_wait();
  sec_mmio_check_values(rnd_uint32());
  sec_mmio_check_counters(1);

  // Disable access to silicon creator info pages and OTP partitions until next
  // reset.
  flash_ctrl_creator_info_pages_lockdown();
  otp_creator_sw_cfg_lockdown();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioCreatorInfoPagesLockdown +
                           kOtpSecMmioCreatorSwCfgLockDown);

  // Configure address translation, compute the epmp regions and the entry
  // point for the virtual address in case the address translation is enabled.
  // Otherwise, compute the epmp regions and the entry point for the load
  // address.
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
      rom_ext_epmp_unlock_owner_stage_r(
          (epmp_region_t){.start = (uintptr_t)_owner_virtual_start_address,
                          .end = (uintptr_t)_owner_virtual_start_address +
                                 (uintptr_t)_owner_virtual_size});
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

  // Unlock execution of owner stage executable code (text) sections.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  rom_ext_epmp_unlock_owner_stage_rx(text_region);
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Jump to OWNER entry point.
  OT_DISCARD(rom_printf("entry: 0x%x\r\n", (unsigned int)entry_point));
  ((owner_stage_entry_point *)entry_point)();

  return kErrorRomExtBootFailed;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_next_boot_bl0_slot_handler(
    boot_svc_msg_t *boot_svc_msg, const boot_data_t *boot_data) {
  uint32_t msg_bl0_slot = boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;
  const manifest_t *kNextSlot;
  switch (launder32(msg_bl0_slot)) {
    case kBootSvcNextBootBl0SlotA:
      HARDENED_CHECK_EQ(msg_bl0_slot, kBootSvcNextBootBl0SlotA);
      kNextSlot = rom_ext_boot_policy_manifest_a_get();
      break;
    case kBootSvcNextBootBl0SlotB:
      HARDENED_CHECK_EQ(msg_bl0_slot, kBootSvcNextBootBl0SlotB);
      kNextSlot = rom_ext_boot_policy_manifest_b_get();
      break;
    default:
      HARDENED_TRAP();
  }

  boot_svc_next_boot_bl0_slot_res_init(kErrorOk,
                                       &boot_svc_msg->next_boot_bl0_slot_res);

  HARDENED_RETURN_IF_ERROR(rom_ext_verify(kNextSlot, boot_data));
  // Boot fails if a verified ROM_EXT cannot be booted.
  HARDENED_RETURN_IF_ERROR(rom_ext_boot(kNextSlot));
  // `rom_ext_boot()` should never return `kErrorOk`, but if it does
  // we must shut down the chip instead of trying the next ROM_EXT.
  return kErrorRomExtBootFailed;
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
      default:
        HARDENED_TRAP();
    }
  }

  rom_ext_boot_policy_manifests_t manifests =
      rom_ext_boot_policy_manifests_get(&boot_data);
  rom_error_t error = kErrorRomExtBootFailed;
  for (size_t i = 0; i < ARRAYSIZE(manifests.ordered); ++i) {
    error = rom_ext_verify(manifests.ordered[i], &boot_data);
    if (error != kErrorOk) {
      continue;
    }

    boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;
    RETURN_IF_ERROR(boot_log_check(boot_log));
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

  return error;
}

void rom_ext_main(void) {
  rom_ext_check_rom_expectations();
  rom_ext_init();
  OT_DISCARD(rom_printf("Starting ROM_EXT\r\n"));
  rom_error_t error = rom_ext_try_boot();
  // If the boot failed, enter bootstrap if it's enabled.
  if (launder32(error) != kErrorOk &&
      launder32(rom_ext_bootstrap_enabled()) == kHardenedBoolTrue) {
    HARDENED_CHECK_NE(error, kErrorOk);
    HARDENED_CHECK_EQ(rom_ext_bootstrap_enabled(), kHardenedBoolTrue);
    shutdown_finalize(rom_ext_bootstrap());
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
