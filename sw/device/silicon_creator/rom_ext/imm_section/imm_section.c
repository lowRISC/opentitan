// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/imm_section/imm_section.h"

#include "hw/top/dt/otp_ctrl.h"  // Generated.
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/coverage/api.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr_dpe.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/rom_ext/imm_section/imm_section_epmp.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.

/**
 * Checks if the keymgr_dpe is enabled by the OTP
 *
 * TODO(#30811): Read DISABLE_KEYMGR_DPE field to jump the CreatorRootKey
 * generation in the ROM section.
 *
 * @return kHardenedBoolTrue if the keymgr_dpe is enabled, kHardenedBoolFalse
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
static hardened_bool_t imm_section_keymgr_dpe_enabled(void) {
  // TODO(#30811): Read DISABLE_KEYMGR_DPE field to jump the CreatorRootKey
  // generation in the ROM section.
  return kHardenedBoolTrue;
}

/**
 * Returns whether the SECRET2 OTP partition has been locked.
 */
OT_WARN_UNUSED_RESULT
static hardened_bool_t imm_section_secret2_locked(void) {
  uint32_t base = dt_otp_ctrl_primary_reg_block(kDtOtpCtrl);
  uint32_t digest_lo =
      sec_mmio_read32(base + OTP_CTRL_SECRET2_DIGEST_0_REG_OFFSET);
  uint32_t digest_hi =
      sec_mmio_read32(base + OTP_CTRL_SECRET2_DIGEST_1_REG_OFFSET);
  if (launder32(digest_lo) == 0 && launder32(digest_hi) == 0) {
    return kHardenedBoolFalse;
  }
  HARDENED_CHECK_NE(digest_lo | digest_hi, 0);
  return kHardenedBoolTrue;
}

OT_WARN_UNUSED_RESULT
static rom_error_t imm_section_start(void) {
  // Check the ePMP state.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  // Check sec_mmio expectations.
  // We don't check the counters since we don't want to tie ROM_EXT to a
  // specific ROM version.
  sec_mmio_check_values(rnd_uint32());

  // Initialize Immutable ROM EXT.
  sec_mmio_next_stage_init();
  HARDENED_RETURN_IF_ERROR(imm_section_epmp_reconfigure());

  // Establish our identity.
  const manifest_t *rom_ext = rom_ext_manifest();

  // Lockdown the attestation seed to readonly as soon as possible to prevent
  // key tampering and exfiltration.
  nvm_ctrl_cert_info_page_creator_cfg(kNvmInfoPageAttestationKeySeeds);
  nvm_ctrl_cert_info_page_owner_restrict(kNvmInfoPageAttestationKeySeeds);
  nvm_ctrl_info_cfg_lock(kNvmInfoPageAttestationKeySeeds);

  // TODO(#30811): Read DISABLE_KEYMGR_DPE field to jump the CreatorRootKey
  // generation in the ROM section.
  hardened_bool_t keymgr_dpe_enabled = imm_section_keymgr_dpe_enabled();
  hardened_bool_t secret2_locked = imm_section_secret2_locked();
  if (launder32(keymgr_dpe_enabled) == kHardenedBoolTrue) {
    HARDENED_CHECK_EQ(keymgr_dpe_enabled, kHardenedBoolTrue);

    // Without a locked SECRET2 partition the hardware does not release the
    // creator root key, which results in a fatal error if the keymgr dpe
    // invokes any derivation operation. Thus leave the keymgr_dpe in reset and
    // let the next stage run.
    if (launder32(secret2_locked) == kHardenedBoolTrue) {
      HARDENED_CHECK_EQ(secret2_locked, kHardenedBoolTrue);

      // Take the entropy complex out of the boot-time mode configured by
      // `rom_start.S`: OTBN needs EDN1 for the key generation below.
      HARDENED_RETURN_IF_ERROR(dice_chain_entropy_complex_init());

      // Generate the certificate related to UDS
      HARDENED_RETURN_IF_ERROR(dice_chain_attestation_creator_keygen());

      // Sideload sealing key to KMAC hw keyslot.
      HARDENED_RETURN_IF_ERROR(ownership_seal_init());

      HARDENED_RETURN_IF_ERROR(dice_chain_init());
      HARDENED_RETURN_IF_ERROR(dice_chain_immutable_section_check());

      // The keymgr_dpe has loaded the attestation and sealing CreatorRootKey
      // inside the designated slots
      HARDENED_RETURN_IF_ERROR(dice_chain_attestation_owner_int(
          &boot_measurements.rom_ext, rom_ext));

      // TODO(#30759): Verify the kKeymgrDPESealSlot / kKeymgrDPEAttestSlot
      // hold keys with boot stage set to BootStageOwner (2). (Note: Current
      // bootstage + 1)
    } else {
      HARDENED_CHECK_EQ(secret2_locked, kHardenedBoolFalse);
      // TODO(#30830): Gracefully handle if secret2 is not locked. This option
      // should not brick the ROM code.
    }
  } else {
    HARDENED_CHECK_EQ(keymgr_dpe_enabled, kHardenedBoolFalse);
    // TODO(#30811): Fallback solution: Only generate the attestation
    // CreatorRootKey here
    // 1. Start the entropy complex
    // 2. load the UDS
    // 3. Generate the attestation Creator Root Key
    // 4. Generate the attestation Owner Int Key
    // 5. Generate the sealing Owner Int Key (Base: either att. Creator Root Key
    // or UDS)
  }

  // Make mutable part executable.
  HARDENED_RETURN_IF_ERROR(imm_section_epmp_mutable_rx(rom_ext));

  return kErrorOk;
}

void imm_section_main(void) {
  rom_error_t error = imm_section_start();

  // If there's an error, this hardened check will trigger the irq handler
  // in ROM to shutdown.
  HARDENED_CHECK_EQ(error, kErrorOk);

  coverage_report();
  coverage_invalidate();

  // Go back to ROM / Mutable ROM_EXT.
  return;
}
