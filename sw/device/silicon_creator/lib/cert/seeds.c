// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/cert/seeds.h"

#include <string.h>

#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"

rom_error_t load_attestation_keygen_seed(uint32_t additional_seed_idx,
                                         uint32_t *seed) {
  uint32_t seed_flash_offset =
      0 + (additional_seed_idx * kAttestationSeedBytes);
  rom_error_t err =
      flash_ctrl_info_read(&kFlashCtrlInfoPageAttestationKeySeeds,
                           seed_flash_offset, kAttestationSeedWords, seed);

  if (err != kErrorOk) {
    flash_ctrl_error_code_t flash_ctrl_err_code;
    flash_ctrl_error_code_get(&flash_ctrl_err_code);
    if (flash_ctrl_err_code.rd_err) {
      // If we encountered a read error, this means the attestation seed page
      // has not been provisioned yet. Clear the seed and continue.
      memset(seed, 0, kAttestationSeedBytes);
      return kErrorOk;
    }
    return err;
  }

  return kErrorOk;
}
