// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/nvm_ctrl.h"

OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_keygen_seed(uint32_t seed_idx,
                                              uint32_t *seed) {
  // Read seed from the attestation key seeds info page. If the page has not
  // been provisioned yet, this returns all-zero words, which will simply
  // result in generating an invalid identity.
  uint32_t seed_offset = 0 + (seed_idx * kAttestationSeedBytes);
  return nvm_ctrl_info_read_zeros_on_read_error(kNvmInfoPageAttestationKeySeeds,
                                                seed_offset,
                                                kAttestationSeedWords, seed);
}
