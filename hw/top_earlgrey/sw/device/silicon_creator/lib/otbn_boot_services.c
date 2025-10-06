// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_keygen_seed(uint32_t seed_idx,
                                              uint32_t *seed) {
  // Read seed from flash info page.
  uint32_t seed_flash_offset = 0 + (seed_idx * kAttestationSeedBytes);
  rom_error_t err =
      flash_ctrl_info_read(&kFlashCtrlInfoPageAttestationKeySeeds,
                           seed_flash_offset, kAttestationSeedWords, seed);

  if (err != kErrorOk) {
    flash_ctrl_error_code_t flash_ctrl_err_code;
    flash_ctrl_error_code_get(&flash_ctrl_err_code);
    if (flash_ctrl_err_code.rd_err) {
      // If we encountered a read error, this means the attestation seed page
      // has not been provisioned yet. In this case, we clear the seed and
      // continue, which will simply result in generating an invalid identity.
      memset(seed, 0, kAttestationSeedBytes);
      return kErrorOk;
    }
    return err;
  }

  return kErrorOk;
}
