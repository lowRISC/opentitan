// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext_verify.h"

#include <string.h>

#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/isfb.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"
#include "sw/device/silicon_creator/lib/ownership/owner_verify.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/usage_constraints.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"

OT_WARN_UNUSED_RESULT
rom_error_t rom_ext_verify(const manifest_t *manifest,
                           const boot_data_t *boot_data, uint32_t *flash_exec,
                           owner_application_keyring_t *keyring,
                           size_t *verify_key, owner_config_t *owner_config,
                           uint32_t *isfb_check_count) {
  RETURN_IF_ERROR(rom_ext_boot_policy_manifest_check(manifest, boot_data));

  uint32_t key_id =
      sigverify_ecdsa_p256_key_id_get(&manifest->ecdsa_public_key);
  // Check if there is an SPX+ key.
  const manifest_ext_spx_key_t *ext_spx_key;
  const manifest_ext_spx_signature_t *ext_spx_signature;
  rom_error_t spx_err = manifest_ext_get_spx_key(manifest, &ext_spx_key);
  spx_err += manifest_ext_get_spx_signature(manifest, &ext_spx_signature);
  switch ((uint32_t)spx_err) {
    case kErrorOk * 2:
      // Both extensions present: valid SPX+ signature.
      key_id ^= sigverify_spx_key_id_get(&ext_spx_key->key);
      break;
    case kErrorManifestBadExtension * 2:
      // Both extensions absent: ECDSA only.
      break;
    default:
      // One present, one absent: bad configuration.
      return kErrorManifestBadExtension;
  }

  RETURN_IF_ERROR(owner_keyring_find_key(keyring, key_id, verify_key));
  uint32_t key_alg = keyring->key[*verify_key]->key_alg;

  dbg_printf("verify: key=%u;%C;%C\r\n", (uint32_t)*verify_key, key_alg,
             keyring->key[*verify_key]->key_domain);

  memset(boot_measurements.bl0.data, (int)rnd_uint32(),
         sizeof(boot_measurements.bl0.data));

  hmac_sha256_init();
  // Hash usage constraints.
  manifest_usage_constraints_t usage_constraints_from_hw;
  sigverify_usage_constraints_get(
      manifest->usage_constraints.selector_bits |
          keyring->key[*verify_key]->usage_constraint,
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

  RETURN_IF_ERROR(owner_verify(
      key_alg, &keyring->key[*verify_key]->data, &manifest->ecdsa_signature,
      &ext_spx_signature->signature, &usage_constraints_from_hw,
      sizeof(usage_constraints_from_hw), NULL, 0, digest_region.start,
      digest_region.length, &act_digest, flash_exec));

  // Perform ISFB checks if the extension is present.
  if ((hardened_bool_t)owner_config->isfb != kHardenedBoolFalse) {
    const manifest_ext_isfb_t *ext_isfb;
    rom_error_t error = manifest_ext_get_isfb(manifest, &ext_isfb);
    if (error == kErrorOk) {
      *isfb_check_count = kHardenedBoolFalse;
      RETURN_IF_ERROR(
          isfb_boot_request_process(ext_isfb, owner_config, isfb_check_count));
      // The previous function returns `kErrorOwnershipISFBFailed` if the strike
      // check or product expression check fails. The following check is to
      // detect any faults.
      HARDENED_CHECK_EQ(*isfb_check_count, isfb_expected_count_get(ext_isfb));
    } else {
      HARDENED_CHECK_NE(error, kErrorOk);
    }
  }

  // This is given that we are expected to perform redundant checks on
  // `flash_exec` and `isfb_check_count`. This is also the reason why don't use
  // `HARDENED_RETURN_IF_ERROR` in the `owner_verify` and `isfb_boot_request`
  // calls.
  return kErrorOk;
}
