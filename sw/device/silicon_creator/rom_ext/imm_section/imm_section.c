// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/imm_section/imm_section.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/rom_ext/imm_section/imm_section_epmp.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_manifest.h"

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

  // Lockdown the attestation seed to readonly as soon as possible to prevent
  // key tampering and exfiltration.
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_owner_restrict(
      &kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_info_cfg_lock(&kFlashCtrlInfoPageAttestationKeySeeds);

  // Establish our identity.
  const manifest_t *rom_ext = rom_ext_manifest();
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_silicon());

  // Sideload sealing key to KMAC hw keyslot.
  HARDENED_RETURN_IF_ERROR(ownership_seal_init());

  HARDENED_RETURN_IF_ERROR(
      dice_chain_attestation_creator(&boot_measurements.rom_ext, rom_ext));

  // Make mutable part executable.
  HARDENED_RETURN_IF_ERROR(imm_section_epmp_mutable_rx(rom_ext));

  return kErrorOk;
}

void imm_section_main(void) {
  rom_error_t error = imm_section_start();

  // If there's an error, this hardened check will trigger the irq handler
  // in ROM to shutdown.
  HARDENED_CHECK_EQ(error, kErrorOk);

  // Go back to ROM / Mutable ROM_EXT.
  return;
}
