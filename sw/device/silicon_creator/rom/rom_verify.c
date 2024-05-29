// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom/rom_verify.h"

#include <assert.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/cfi.h"
#include "sw/device/silicon_creator/lib/chip_info.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/rom/boot_policy.h"
#include "sw/device/silicon_creator/rom/rom_cfi.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_ecdsa_p256.h"
#include "sw/device/silicon_creator/rom/sigverify_keys_spx.h"
#include "sw/device/silicon_creator/rom/sigverify_otp_keys.h"

rom_error_t rom_verify(const manifest_t *manifest,
                       const lifecycle_state_t lc_state,
                       const boot_data_t *boot_data,
                       const sigverify_otp_key_ctx_t *sigverify_ctx,
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
      boot_data->min_security_version_rom_ext) {
    anti_rollback = &extra_word;
    anti_rollback_len = sizeof(extra_word);
  }
  *flash_exec = 0;
  HARDENED_RETURN_IF_ERROR(boot_policy_manifest_check(manifest, boot_data));

  // Load OTBN boot services app.
  //
  // This will be reused by later boot stages.
  HARDENED_RETURN_IF_ERROR(otbn_boot_app_load());
  CFI_FUNC_COUNTER_INCREMENT(rom_counters, kCfiRomVerify, 1);

  // ECDSA key.
  const sigverify_ecdsa_p256_buffer_t *ecdsa_key = NULL;
  HARDENED_RETURN_IF_ERROR(sigverify_ecdsa_p256_key_get(
      sigverify_ctx,
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
        sigverify_ctx, sigverify_spx_key_id_get(&ext_spx_key->key), lc_state,
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
                    boot_data->min_security_version_rom_ext);
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
