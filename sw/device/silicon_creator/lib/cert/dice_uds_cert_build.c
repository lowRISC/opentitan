// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/template.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"

// Check that the UDS template fits within our perso blob
static_assert(kUdsMaxTbsSizeBytes <= kDiceUdsMaxTbsSizeBytes,
              "UDS TBS template too large for personalization");
static_assert(kUdsMaxCertSizeBytes <= kDiceUdsMaxCertSizeBytes,
              "UDS cert template too large for personalization");

// The `dice_*_cert_build` libraries are only used for x509 certificates
// (both ECDSA and ML-DSA). CWT is handled separately in `dice_cwt.c`
const dice_cert_format_t kDiceCertFormat = kDiceCertFormatX509TcbInfo;

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

rom_error_t dice_uds_tbs_cert_build(
    const hmac_digest_t *otp_creator_sw_cfg_measurement,
    const hmac_digest_t *otp_owner_sw_cfg_measurement,
    const hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    const hmac_digest_t *otp_rot_creator_auth_state_measurement,
    const cert_key_id_pair_t *key_ids,
    const ecdsa_p256_public_key_t *uds_pubkey, uint8_t *tbs_cert,
    size_t *tbs_cert_size) {
  // Generate the TBS certificate.
  uds_tbs_values_t uds_tbs_params = {0};

  uds_tbs_params.creator_pub_key_alg = kUdsKeygenAlgEcdsaP256;
  uds_tbs_params.signature_alg = kUdsSignatureAlgEcdsaP256;

  TEMPLATE_SET(uds_tbs_params, Uds, OtpCreatorSwCfgHash,
               otp_creator_sw_cfg_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpOwnerSwCfgHash,
               otp_owner_sw_cfg_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpRotCreatorAuthCodesignHash,
               otp_rot_creator_auth_codesign_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, OtpRotCreatorAuthStateHash,
               otp_rot_creator_auth_state_measurement->digest);
  TEMPLATE_SET(uds_tbs_params, Uds, DebugFlag, is_debug_exposed());
  TEMPLATE_SET(uds_tbs_params, Uds, CreatorPubKeyEcX, uds_pubkey->x);
  TEMPLATE_SET(uds_tbs_params, Uds, CreatorPubKeyEcY, uds_pubkey->y);

  TEMPLATE_SET_TRUNCATED(uds_tbs_params, Uds, CreatorPubKeyId,
                         key_ids->cert->digest, kCertKeyIdSizeInBytes);
  TEMPLATE_SET_TRUNCATED(uds_tbs_params, Uds, AuthKeyKeyId,
                         key_ids->endorsement->digest, kCertKeyIdSizeInBytes);

  HARDENED_RETURN_IF_ERROR(
      uds_build_tbs(&uds_tbs_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}
