// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/dice_mldsa.h"
#include "sw/device/silicon_creator/lib/cert/dice_mldsa_keys.h"
#include "sw/device/silicon_creator/lib/cert/template.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/mldsa_key.h"
#include "third_party/embedpqc/mldsa44_tiny.h"
#include "third_party/embedpqc/mldsa87_tiny.h"
#include "third_party/embedpqc/ports/mldsa44_tiny_caller.h"
#include "third_party/embedpqc/ports/mldsa87_tiny_caller.h"

// This stack need to be word aligned as well for `hardened_memshred` operations
static uint8_t dice_mldsa_perso_scratch_stack[kDiceMldsaPersoScratchBufferSize]
    __attribute__((aligned(16)));

static_assert(
    (kDiceMldsaPersoScratchBufferSize % 16) == 0,
    "kDiceMldsaPersoScratchBufferSize must be aligned to 16-bytes and "
    "its size must be multiple of 16-bytes since end of this buffer is used as "
    "`sp`, and RISC-V ABI documentation mentions: 'In the standard RISC-V "
    "calling convention, the stack grows downward and the stack pointer is "
    "always kept 16-byte aligned'");

// Copied from `dice_uds_cert_build.c`
/**
 * Returns true if debug (JTAG) access is exposed in the current LC state.
 */
static bool is_debug_exposed(void) {
  lifecycle_state_t lc_state = lifecycle_state_get();
  if (lc_state == kLcStateProd || lc_state == kLcStateProdEnd) {
    return false;
  }
  return true;
}

static rom_error_t dice_uds_mldsa_tbs_cert_build(
    const hmac_digest_t *otp_creator_sw_cfg_measurement,
    const hmac_digest_t *otp_owner_sw_cfg_measurement,
    const hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    const hmac_digest_t *otp_rot_creator_auth_state_measurement,
    const cert_key_id_pair_t *key_ids, const mldsa_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  // Use template generation code based on fields defined `uds.hjson`
  uds_tbs_values_t uds_tbs_params = {0};
  if (uds_pubkey->param_set == kMldsaParameterSet44) {
    uds_tbs_params.creator_pub_key_alg = kUdsKeygenAlgMldsa44;
    TEMPLATE_SET(uds_tbs_params, Uds, CreatorPubKeyMldsa44,
                 uds_pubkey->key.key_44.key);
  } else if (uds_pubkey->param_set == kMldsaParameterSet87) {
    uds_tbs_params.creator_pub_key_alg = kUdsKeygenAlgMldsa87;
    TEMPLATE_SET(uds_tbs_params, Uds, CreatorPubKeyMldsa87,
                 uds_pubkey->key.key_87.key);
  } else {
    return kErrorCertInvalidArgument;
  }
  uds_tbs_params.signature_alg = kUdsSignatureAlgMldsa87;
  TEMPLATE_SET(uds_tbs_params, Uds, OtpCreatorSwCfgHash,
               otp_creator_sw_cfg_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpOwnerSwCfgHash,
               otp_owner_sw_cfg_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpRotCreatorAuthCodesignHash,
               otp_rot_creator_auth_codesign_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpRotCreatorAuthStateHash,
               otp_rot_creator_auth_state_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, DebugFlag, is_debug_exposed());

  TEMPLATE_SET_TRUNCATED(uds_tbs_params, Uds, CreatorPubKeyId,
                         key_ids->cert->digest, kCertKeyIdSizeInBytes);
  TEMPLATE_SET_TRUNCATED(uds_tbs_params, Uds, AuthKeyKeyId,
                         key_ids->endorsement->digest, kCertKeyIdSizeInBytes);

  HARDENED_RETURN_IF_ERROR(
      uds_build_tbs(&uds_tbs_params, tbs_cert, tbs_cert_size));
  return kErrorOk;
}

rom_error_t dice_uds_mldsa_tbs_cert_generate_and_build(
    const hmac_digest_t *otp_creator_sw_cfg_measurement,
    const hmac_digest_t *otp_owner_sw_cfg_measurement,
    const hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    const hmac_digest_t *otp_rot_creator_auth_state_measurement,
    const cert_key_id_pair_t *key_ids, mldsa_parameter_set_t mldsa_params_set,
    uint8_t *tbs_cert_buffer, size_t *tbs_cert_size) {
  // Generate UDS seed for keygen. Destroy this as soon as possible once it is
  // no longer needed
  keymgr_binding_value_t uds_mldsa_seed;
  static_assert(sizeof(uds_mldsa_seed.data) % sizeof(uint32_t) == 0,
                "Expect seed size to be multiple of word size, otherwise "
                "hardened memshred will leave few bytes untouched");

  static mldsa_public_key_t mldsa_pubkey;
  uint32_t *stack_top = (uint32_t *)(dice_mldsa_perso_scratch_stack +
                                     sizeof(dice_mldsa_perso_scratch_stack));
  if (mldsa_params_set == kMldsaParameterSet44) {
    // Generate UDS MLDSA-44 public key
    mldsa_pubkey.param_set = kMldsaParameterSet44;
    HARDENED_RETURN_IF_ERROR_WITH_CLEANUP_ATTEMPT(
        dice_mldsa_derive_seed(&kDiceMldsaUdsKeygenParams,
                               mldsa_pubkey.param_set, &uds_mldsa_seed),
        hardened_memshred(uds_mldsa_seed.data,
                          sizeof(uds_mldsa_seed.data) / sizeof(uint32_t)));
    mldsa44_tiny_pub_from_seed_with_stack(mldsa_pubkey.key.key_44.key,
                                          (const uint8_t *)uds_mldsa_seed.data,
                                          stack_top);
  } else if (mldsa_params_set == kMldsaParameterSet87) {
    // Generate UDS MLDSA-87 public key
    mldsa_pubkey.param_set = kMldsaParameterSet87;
    HARDENED_RETURN_IF_ERROR_WITH_CLEANUP_ATTEMPT(
        dice_mldsa_derive_seed(&kDiceMldsaUdsKeygenParams,
                               mldsa_pubkey.param_set, &uds_mldsa_seed),
        hardened_memshred(uds_mldsa_seed.data,
                          sizeof(uds_mldsa_seed.data) / sizeof(uint32_t)));
    mldsa87_tiny_pub_from_seed_with_stack(mldsa_pubkey.key.key_87.key,
                                          (const uint8_t *)uds_mldsa_seed.data,
                                          stack_top);
  } else {
    HARDENED_CHECK_EQ(
        hardened_memshred(uds_mldsa_seed.data,
                          sizeof(uds_mldsa_seed.data) / sizeof(uint32_t))
            .value,
        kHardenedBoolTrue);
    return kErrorCertInvalidArgument;
  }

  // Populate UDS MLDSA pubkey ID
  dice_mldsa_key_id_get((const hmac_key_t *)uds_mldsa_seed.data, key_ids->cert);

  // Delete the seed since it is no longer needed
  HARDENED_CHECK_EQ(
      hardened_memshred(uds_mldsa_seed.data,
                        sizeof(uds_mldsa_seed.data) / sizeof(uint32_t))
          .value,
      kHardenedBoolTrue);

  static_assert(
      (sizeof(dice_mldsa_perso_scratch_stack) % sizeof(uint32_t)) == 0,
      "Scratch stack size must be multiple of 4 for hardened_memshred");
  // Clear any secret data on the stack
  HARDENED_CHECK_EQ(
      hardened_memshred(
          (uint32_t *)dice_mldsa_perso_scratch_stack,
          sizeof(dice_mldsa_perso_scratch_stack) / sizeof(uint32_t))
          .value,
      kHardenedBoolTrue);
  HARDENED_RETURN_IF_ERROR(kmac_keymgr_configure());

  // Build UDS MLDSA certificate for signing
  return dice_uds_mldsa_tbs_cert_build(
      otp_creator_sw_cfg_measurement, otp_owner_sw_cfg_measurement,
      otp_rot_creator_auth_codesign_measurement,
      otp_rot_creator_auth_state_measurement, key_ids, &mldsa_pubkey,
      tbs_cert_buffer, tbs_cert_size);
}
