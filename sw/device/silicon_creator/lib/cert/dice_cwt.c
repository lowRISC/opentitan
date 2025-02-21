// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cbor.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/cwt_cose_key.h"
#include "sw/device/silicon_creator/lib/cert/cwt_dice_chain_entry.h"
#include "sw/device/silicon_creator/lib/cert/cwt_dice_chain_entry_input.h"
#include "sw/device/silicon_creator/lib/cert/cwt_dice_chain_entry_payload.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "otp_ctrl_regs.h"  // Generated.

const dice_cert_format_t kDiceCertFormat = kDiceCertFormatCWTAndroid;

enum config_desc_labels {
  kSecurityVersionLabel = -70005,
  // Implementataion specific value,
  // less than -65536 and outside of [-70000, -70999]
  kOwnerManifestMeasurmentLabel = -71006,
};

enum payload_entry_sizes {
  // The length of Profile Name
  kProfileNameLength = 10,
  // The Key ID length, which equals to the SHA256 digest size in bytes
  kIssuerSubjectKeyIdLength = kHmacDigestNumBytes,
  // The size of issuer & subject name, which equals to the ascii size
  // transformed form Key ID.
  kIssuerSubjectNameLength = kIssuerSubjectKeyIdLength * 2,
  // 64 byte should be enough for 2 entries
  kConfigDescBuffSize = 64,
};

// Simple object to put all "configuration descriptor" variables together
typedef struct {
  uint8_t *buf;
  size_t *buf_size;
  hmac_digest_t *d;
} config_desc_t;

// a0    # map(0)
const uint8_t kCborMap0[] = {0xa0};
#define CWT_PROFILE_NAME "android.16"

// Debug=2, Normal=1
static uint8_t get_chip_mode(void) {
  return ((lifecycle_state_get() == kLcStateProd) ? 1 : 2);
}

static void fill_dice_id_string(
    const uint8_t dice_id[kIssuerSubjectKeyIdLength],
    char dice_id_str[kIssuerSubjectNameLength + 1]) {
  size_t idx;
  for (idx = 0; idx < kIssuerSubjectKeyIdLength; idx++, dice_id_str += 2)
    util_hexdump_byte(dice_id[idx], (uint8_t *)dice_id_str);
}

static rom_error_t configuration_descriptor_build(
    config_desc_t *config_desc, const size_t sec_version,
    const hmac_digest_t *manifest_measurement) {
  struct CborOut kCborOutHandle;
  struct CborOut *pCborOut = &kCborOutHandle;
  HARDENED_RETURN_IF_ERROR(
      cbor_write_out_init(pCborOut, config_desc->buf, *config_desc->buf_size));
  HARDENED_RETURN_IF_ERROR(
      cbor_map_init(pCborOut, (manifest_measurement != NULL) ? 2 : 1));
  HARDENED_RETURN_IF_ERROR(
      cbor_write_pair_int_uint(pCborOut, kSecurityVersionLabel, sec_version));
  if (manifest_measurement != NULL)
    HARDENED_RETURN_IF_ERROR(cbor_write_pair_int_bytes(
        pCborOut, kOwnerManifestMeasurmentLabel,
        (uint8_t *)manifest_measurement->digest, kHmacDigestNumBytes));
  *config_desc->buf_size = CborOutSize(pCborOut);

  return kErrorOk;
}

rom_error_t dice_uds_tbs_cert_build(
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    cert_key_id_pair_t *key_ids, ecdsa_p256_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  cwt_cose_key_values_t cwt_cose_key_params = {
      .pub_key_ec_x = (uint8_t *)uds_pubkey->x,
      .pub_key_ec_x_size = sizeof(uds_pubkey->x),
      .pub_key_ec_y = (uint8_t *)uds_pubkey->y,
      .pub_key_ec_y_size = sizeof(uds_pubkey->y),
  };
  // For DICE CWT implementation, no need to sign UDS_Pub but just a COSE_Key
  // structure.
  // Those otp_*measurement parameters exist just for API alignment between
  // different implementations.
  HARDENED_RETURN_IF_ERROR(
      cwt_cose_key_build(&cwt_cose_key_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}

static rom_error_t dice_cwt_cdi_build(hmac_digest_t *image_measurement,
                                      const config_desc_t *config_desc,
                                      cert_key_id_pair_t *key_ids,
                                      ecdsa_p256_public_key_t *cdi_pubkey,
                                      uint8_t *cert, size_t *cert_size) {
  // Build Subject public key structure
  uint8_t cose_key_buffer[kCwtCoseKeyMaxVariableSizeBytes] = {0};
  size_t cose_key_size = sizeof(cose_key_buffer);
  cwt_cose_key_values_t cwt_cose_key_params = {
      .pub_key_ec_x = (uint8_t *)cdi_pubkey->x,
      .pub_key_ec_x_size = sizeof(cdi_pubkey->x),
      .pub_key_ec_y = (uint8_t *)cdi_pubkey->y,
      .pub_key_ec_y_size = sizeof(cdi_pubkey->y),
  };
  HARDENED_RETURN_IF_ERROR(cwt_cose_key_build(&cwt_cose_key_params,
                                              cose_key_buffer, &cose_key_size));

  // Try to generate DiceChainEntryPayload
  char issuer[kIssuerSubjectNameLength + 1] = {0};
  char subject[kIssuerSubjectNameLength + 1] = {0};
  fill_dice_id_string((uint8_t *)(key_ids->endorsement->digest), issuer);
  fill_dice_id_string((uint8_t *)(key_ids->cert->digest), subject);

  uint8_t entry_payload_buffer[kCwtDiceChainEntryPayloadMaxVariableSizeBytes] =
      {0};
  size_t entry_payload_size = sizeof(entry_payload_buffer);

  // Compute Authority Hash against an empty map since it's mandatory but
  // "Authority Descriptor" isn't.
  hmac_digest_t auth_hash;
  hmac_sha256(kCborMap0, sizeof(kCborMap0), &auth_hash);
  util_reverse_bytes(auth_hash.digest, kHmacDigestNumBytes);

  uint8_t mode = get_chip_mode();
  cwt_dice_chain_entry_payload_values_t cwt_dice_chain_entry_payload_params = {
      .auth_hash = (uint8_t *)auth_hash.digest,
      .auth_hash_size = kHmacDigestNumBytes,
      .code_hash = (uint8_t *)image_measurement->digest,
      .code_hash_size = kHmacDigestNumBytes,
      .subject = subject,
      .subject_size = kIssuerSubjectNameLength,
      .mode = &mode,
      .mode_size = sizeof(mode),
      .issuer = issuer,
      .issuer_size = kIssuerSubjectNameLength,
      .subject_pk = cose_key_buffer,
      .subject_pk_size = cose_key_size,
      .config_desc = config_desc->buf,
      .config_desc_size = *config_desc->buf_size,
      .config_hash = (uint8_t *)config_desc->d->digest,
      .config_hash_size = kHmacDigestNumBytes,
      .profile_name = CWT_PROFILE_NAME,
      .profile_name_size = kProfileNameLength};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_payload_build(
      &cwt_dice_chain_entry_payload_params, entry_payload_buffer,
      &entry_payload_size));

  // Try to generate DiceChainEntryInput, by reusing the cert buffer.
  size_t cdi_entry_input_size = kCwtDiceChainEntryInputMaxVariableSizeBytes;
  if (cdi_entry_input_size > *cert_size)
    return kErrorCertInvalidSize;
  cwt_dice_chain_entry_input_values_t cwt_dice_chain_entry_input_params = {
      .payload = entry_payload_buffer, .payload_size = entry_payload_size};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_input_build(
      &cwt_dice_chain_entry_input_params, cert, &cdi_entry_input_size));

  // Obtain digest & sign
  ecdsa_p256_signature_t curr_tbs_signature;
  hmac_digest_t tbs_digest;
  hmac_sha256(cert, cdi_entry_input_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  // Build the final DiceEntry
  cwt_dice_chain_entry_values_t cwt_dice_chain_entry_params = {
      .payload = entry_payload_buffer,
      .payload_size = entry_payload_size,
      .signature = (uint8_t *)&curr_tbs_signature,
      .signature_size = sizeof(ecdsa_p256_signature_t)};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_build(
      &cwt_dice_chain_entry_params, cert, cert_size));

  return kErrorOk;
}

static rom_error_t cwt_build(hmac_digest_t *image_measurement,
                             hmac_digest_t *manifest_measurement,
                             uint32_t security_version,
                             cert_key_id_pair_t *key_ids,
                             ecdsa_p256_public_key_t *cdi_pubkey,
                             const sc_keymgr_ecc_key_t *dicekey, uint8_t *cert,
                             size_t *cert_size) {
  uint8_t config_desc_buf[kConfigDescBuffSize];
  size_t config_desc_buf_size = sizeof(config_desc_buf);
  hmac_digest_t config_desc_hash;
  config_desc_t config_desc = {.buf = config_desc_buf,
                               .buf_size = &config_desc_buf_size,
                               .d = &config_desc_hash};
  HARDENED_RETURN_IF_ERROR(configuration_descriptor_build(
      &config_desc, security_version, manifest_measurement));
  hmac_sha256(config_desc.buf, *config_desc.buf_size, config_desc.d);
  util_reverse_bytes(config_desc.d->digest, kHmacDigestNumBytes);

  HARDENED_RETURN_IF_ERROR(dice_cwt_cdi_build(
      image_measurement, &config_desc, key_ids, cdi_pubkey, cert, cert_size));

  // Save the CDI private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      dicekey->keygen_seed_idx, dicekey->type, *dicekey->keymgr_diversifier));

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  return cwt_build(rom_ext_measurement, NULL, rom_ext_security_version, key_ids,
                   cdi_0_pubkey, &kDiceKeyCdi0, cert, cert_size);
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  return cwt_build(owner_measurement, owner_manifest_measurement,
                   owner_security_version, key_ids, cdi_1_pubkey, &kDiceKeyCdi1,
                   cert, cert_size);
}

rom_error_t dice_cert_check_valid(const perso_tlv_cert_obj_t *cert_obj,
                                  const hmac_digest_t *pubkey_id,
                                  const ecdsa_p256_public_key_t *pubkey,
                                  hardened_bool_t *cert_valid_output) {
  // TODO(lowRISC/opentitan:#24281): implement body
  return kErrorOk;
}
