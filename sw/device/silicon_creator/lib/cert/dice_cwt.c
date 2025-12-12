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
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "hw/top/otp_ctrl_regs.h"  // Generated.

const dice_cert_format_t kDiceCertFormat = kDiceCertFormatCWTAndroid;

enum config_desc_labels {
  kSecurityVersionLabel = -70005,
  // Implementataion specific value,
  // less than -65536 and outside of [-70000, -70999]
  kOwnerManifestMeasurmentLabel = -71006,
};

// This input is designed to capture a configuration signal in a stable way,
// and to reflect important decisions a device makes at runtime.
// https://pigweed.googlesource.com/open-dice/+/HEAD/docs/specification.md#mode-value-details
enum open_dice_mode_value {
  kDiceModeNormal = 1,
  kDiceModeDebug = 2,
};

enum payload_entry_sizes {
  // The length of Profile Name
  kProfileNameLength = 10,
  // The Key ID length, which equals to the SHA256 digest size in bytes
  kIssuerSubjectKeyIdLength = kHmacDigestNumBytes,
  // The identifiers are 20 octets (reserve double size for HEX translation) so
  // they fit in the RFC 5280 serialNumber field constraints and the
  // X520SerialNumber type when hex encoded.
  kIssuerSubjectNameLength = 40,
  // 64 byte should be enough for 2 entries
  kConfigDescBuffSize = 64,
};
static_assert(kIssuerSubjectNameLength <= kIssuerSubjectKeyIdLength * 2,
              "Insufficient SubjectNameLength");

enum cwt_cert_expectations {
  // Size of magic bytes to distinguish between CoseKey and CoseSign1 message.
  kDiceCwtMagicSizeBytes = 1,

  // Magic header identifying a CoseKey message (CBOR map with 5 elements).
  kDiceCwtCoseKeyMagic = 0xa5,

  // Size of the CoseKey identity region header. (y-coord)
  // Expects 1B mapKey(-3) + 2B bstr(32) header.
  kDiceCwtCoseKeyIdHeaderSizeBytes = 1 + 2,

  // Total size in bytes of the CoseKey identity region. (y-coord)
  // Expects header + 32B p256 y-coord.
  kDiceCwtCoseKeyIdSizeBytes =
      kDiceCwtCoseKeyIdHeaderSizeBytes + kEcdsaP256PublicKeyCoordBytes,

  // Offset to the CoseKey identity region. (y-coord)
  // This offset is relative to the *end* of CoseKey message.
  kDiceCwtCoseKeyIdOffsetBytes = 0,

  // All valid CoseKey messages should be longer than this size.
  kDiceCwtCoseKeyMinSizeBytes = kDiceCwtMagicSizeBytes +
                                kDiceCwtCoseKeyIdOffsetBytes +
                                kDiceCwtCoseKeyIdSizeBytes,

  // Magic header identifying a CoseSign1 message (CBOR array with 4 elements).
  kDiceCwtCoseSign1Magic = 0x84,

  // Size of the CoseSign1 identity region header. (subject hex id)
  // Expects 1B mapKey(2) + 2B text(64) header.
  kDiceCwtCoseSign1IdHeaderSizeBytes = 1 + 2,

  // Size of the CoseSign1 identity region. (subject hex id)
  // Expects header + 64B subject hex id.
  kDiceCwtCoseSign1IdSizeBytes =
      kDiceCwtCoseSign1IdHeaderSizeBytes + kIssuerSubjectNameLength,

  // Offset to the CoseSign1 identity region. (subject hex id)
  // This offset is relative to the *begin* of CoseSign1.
  // Expects 9B COSE prefix + 4B Payload prefix + 64B issuer id.
  kDiceCwtCoseSign1IdOffsetBytes = 9 + 4 + kIssuerSubjectNameLength,

  // All valid CoseSign1 messages should be longer than this size.
  kDiceCwtCoseSign1MinSizeBytes = kDiceCwtMagicSizeBytes +
                                  kDiceCwtCoseSign1IdOffsetBytes +
                                  kDiceCwtCoseSign1IdSizeBytes,
};

// Reusable buffer for checking cose key identity.
static char expected_cose_key_id[kDiceCwtCoseKeyIdSizeBytes] = {
    0x22,                                 // mapKey -3 (y-coord)
    0x58, kEcdsaP256PublicKeyCoordBytes,  // 32-byte bstr header
    // Remaining bytes will be filled during check.
};

// Reusable buffer for checking cose sign1 cert identity.
static char expected_cose_sign1_id[kDiceCwtCoseSign1IdSizeBytes] = {
    0x02,                            // mapKey 2 (subject id)
    0x78, kIssuerSubjectNameLength,  // 64-byte text header
    // Remaining bytes will be filled during check.
};

// Reusable buffer for generating Configuration Descriptor
static uint8_t config_desc_buf[kConfigDescBuffSize] = {0};
// a0    # map(0)
const uint8_t kCborMap0[] = {0xa0};
// Reusable buffer for generating UDS/CDI_* COSE_Key
static uint8_t cose_key_buffer[kCwtCoseKeyMaxVariableSizeBytes] = {0};
// Reusable buffer for generating signature
static ecdsa_p256_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};

#define CWT_PROFILE_NAME "android.16"

static uint8_t get_chip_mode_cdi0(void) {
  return (lifecycle_is_prod() ? kDiceModeNormal : kDiceModeDebug);
}

static uint8_t get_chip_mode_cdi1(owner_app_domain_t key_domain) {
  if (launder32(key_domain) != kOwnerAppDomainProd) {
    return kDiceModeDebug;
  }
  HARDENED_CHECK_EQ(key_domain, kOwnerAppDomainProd);
  return kDiceModeNormal;
}

static char issuer[kIssuerSubjectNameLength + 1] = {0};
static char subject[kIssuerSubjectNameLength + 1] = {0};

static void fill_dice_id_string(
    const uint8_t dice_id[kIssuerSubjectKeyIdLength],
    char dice_id_str[kIssuerSubjectNameLength + 1]) {
  size_t idx;
  for (idx = 0; idx * 2 < kIssuerSubjectNameLength; idx++, dice_id_str += 2)
    util_hexdump_byte(dice_id[idx], (uint8_t *)&dice_id_str[0]);
}

static rom_error_t configuration_descriptor_build(
    size_t *buf_size, const size_t sec_version,
    const hmac_digest_t *manifest_measurement) {
  cbor_out_t cbor_out;
  cbor_out_init(&cbor_out, config_desc_buf);

  cbor_out_t *ptrs[2] = {NULL, &cbor_out};
  const size_t ptrs_len = sizeof(ptrs) / sizeof(ptrs[0]);

  for (size_t i = 0; i < ptrs_len; ++i) {
    cbor_out_t *cbor = ptrs[i];
    size_t sz = 0;

    sz += cbor_write_map_header(cbor, (manifest_measurement != NULL) ? 2 : 1);
    sz += cbor_write_int(cbor, kSecurityVersionLabel);
    sz += cbor_write_int(cbor, sec_version);

    if (manifest_measurement != NULL) {
      sz += cbor_write_int(cbor, kOwnerManifestMeasurmentLabel);
      sz += cbor_write_bstr(cbor, (uint8_t *)&manifest_measurement->digest[0],
                            kHmacDigestNumBytes);
    }

    if (sz > *buf_size)
      return kErrorCertInvalidSize;
  }

  *buf_size = cbor_out_size(&cbor_out);

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
  OT_DISCARD(otp_creator_sw_cfg_measurement);
  OT_DISCARD(otp_owner_sw_cfg_measurement);
  OT_DISCARD(otp_rot_creator_auth_codesign_measurement);
  OT_DISCARD(otp_rot_creator_auth_state_measurement);
  OT_DISCARD(key_ids);
  HARDENED_RETURN_IF_ERROR(
      cwt_cose_key_build(&cwt_cose_key_params, tbs_cert, tbs_cert_size));

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  // Build Subject public key structure
  size_t cose_key_size = sizeof(cose_key_buffer);
  cwt_cose_key_values_t cwt_cose_key_params = {
      .pub_key_ec_x = (uint8_t *)cdi_0_pubkey->x,
      .pub_key_ec_x_size = sizeof(cdi_0_pubkey->x),
      .pub_key_ec_y = (uint8_t *)cdi_0_pubkey->y,
      .pub_key_ec_y_size = sizeof(cdi_0_pubkey->y),
  };
  HARDENED_RETURN_IF_ERROR(cwt_cose_key_build(
      &cwt_cose_key_params, &cose_key_buffer[0], &cose_key_size));

  // Try to generate DiceChainEntryPayload
  fill_dice_id_string((uint8_t *)(key_ids->endorsement->digest), issuer);
  fill_dice_id_string((uint8_t *)(key_ids->cert->digest), subject);

  uint8_t
      cdi0_entry_payload_buffer[kCwtDiceChainEntryPayloadMaxVariableSizeBytes];
  size_t cdi0_entry_payload_size = sizeof(cdi0_entry_payload_buffer);

  size_t config_desc_buf_size = kConfigDescBuffSize;
  // No extension measurement is needed in CDI_0, just pass a NULL to the
  // config_descriptors to bypass encoding.
  HARDENED_RETURN_IF_ERROR(configuration_descriptor_build(
      &config_desc_buf_size, rom_ext_security_version, NULL));
  hmac_digest_t conf_hash;
  hmac_sha256(config_desc_buf, config_desc_buf_size, &conf_hash);
  util_reverse_bytes(conf_hash.digest, kHmacDigestNumBytes);

  // Compute Authority Hash against an empty map since it's mandatory but
  // "Authority Descriptor" isn't.
  hmac_digest_t auth_hash;
  hmac_sha256(kCborMap0, sizeof(kCborMap0), &auth_hash);
  util_reverse_bytes(auth_hash.digest, kHmacDigestNumBytes);

  uint8_t mode = get_chip_mode_cdi0();
  cwt_dice_chain_entry_payload_values_t cwt_dice_chain_entry_payload_params = {
      .auth_hash = (uint8_t *)&auth_hash.digest[0],
      .auth_hash_size = kHmacDigestNumBytes,
      .code_hash = (uint8_t *)&rom_ext_measurement->digest[0],
      .code_hash_size = kHmacDigestNumBytes,
      .subject = &subject[0],
      .subject_size = kIssuerSubjectNameLength,
      .mode = &mode,
      .mode_size = sizeof(mode),
      .issuer = &issuer[0],
      .issuer_size = kIssuerSubjectNameLength,
      .subject_pk = &cose_key_buffer[0],
      .subject_pk_size = cose_key_size,
      .config_desc = config_desc_buf,
      .config_desc_size = config_desc_buf_size,
      .config_hash = (uint8_t *)&conf_hash.digest[0],
      .config_hash_size = kHmacDigestNumBytes,
      .profile_name = CWT_PROFILE_NAME,
      .profile_name_size = kProfileNameLength};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_payload_build(
      &cwt_dice_chain_entry_payload_params, cdi0_entry_payload_buffer,
      &cdi0_entry_payload_size));

  // Try to generate DiceChainEntryInput, by reusing the cert buffer.
  size_t cdi0_entry_input_size = kCwtDiceChainEntryInputMaxVariableSizeBytes;
  if (cdi0_entry_input_size > *cert_size)
    return kErrorCertInvalidSize;
  cwt_dice_chain_entry_input_values_t cwt_dice_chain_entry_input_params = {
      .payload = cdi0_entry_payload_buffer,
      .payload_size = cdi0_entry_payload_size};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_input_build(
      &cwt_dice_chain_entry_input_params, cert, &cdi0_entry_input_size));

  // Obtain digest & sign
  hmac_digest_t tbs_digest;
  hmac_sha256(cert, cdi0_entry_input_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  // Build the final DiceEntry
  cwt_dice_chain_entry_values_t cwt_dice_chain_entry_params = {
      .payload = cdi0_entry_payload_buffer,
      .payload_size = cdi0_entry_payload_size,
      .signature = (uint8_t *)&curr_tbs_signature,
      .signature_size = sizeof(ecdsa_p256_signature_t)};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_build(
      &cwt_dice_chain_entry_params, cert, cert_size));

  // Save the CDI_0 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
      *kDiceKeyCdi0.keymgr_diversifier));
  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  owner_app_domain_t key_domain,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  // Build Subject public key structure
  size_t cose_key_size = sizeof(cose_key_buffer);
  cwt_cose_key_values_t cwt_cose_key_params = {
      .pub_key_ec_x = (uint8_t *)cdi_1_pubkey->x,
      .pub_key_ec_x_size = sizeof(cdi_1_pubkey->x),
      .pub_key_ec_y = (uint8_t *)cdi_1_pubkey->y,
      .pub_key_ec_y_size = sizeof(cdi_1_pubkey->y),
  };
  HARDENED_RETURN_IF_ERROR(cwt_cose_key_build(
      &cwt_cose_key_params, &cose_key_buffer[0], &cose_key_size));

  // Try to generate DiceChainEntryPayload
  fill_dice_id_string((uint8_t *)(key_ids->endorsement->digest), issuer);
  fill_dice_id_string((uint8_t *)(key_ids->cert->digest), subject);

  uint8_t
      cdi1_entry_payload_buffer[kCwtDiceChainEntryPayloadMaxVariableSizeBytes];
  size_t cdi1_entry_payload_size = sizeof(cdi1_entry_payload_buffer);

  size_t config_desc_buf_size = sizeof(config_desc_buf);
  HARDENED_RETURN_IF_ERROR(configuration_descriptor_build(
      &config_desc_buf_size, owner_security_version,
      owner_manifest_measurement));
  hmac_digest_t conf_hash;
  hmac_sha256(config_desc_buf, config_desc_buf_size, &conf_hash);
  util_reverse_bytes(conf_hash.digest, kHmacDigestNumBytes);

  // Compute Authority Hash against an empty map since it's mandatory but
  // "Authority Descriptor" isn't.
  hmac_digest_t auth_hash;
  hmac_sha256(kCborMap0, sizeof(kCborMap0), &auth_hash);
  util_reverse_bytes(auth_hash.digest, kHmacDigestNumBytes);

  uint8_t mode = get_chip_mode_cdi1(key_domain);
  cwt_dice_chain_entry_payload_values_t cwt_dice_chain_entry_payload_params = {
      .auth_hash = (uint8_t *)&auth_hash.digest[0],
      .auth_hash_size = kHmacDigestNumBytes,
      .code_hash = (uint8_t *)&owner_measurement->digest[0],
      .code_hash_size = kHmacDigestNumBytes,
      .subject = &subject[0],
      .subject_size = kIssuerSubjectNameLength,
      .mode = &mode,
      .mode_size = sizeof(mode),
      .issuer = &issuer[0],
      .issuer_size = kIssuerSubjectNameLength,
      .subject_pk = &cose_key_buffer[0],
      .subject_pk_size = cose_key_size,
      .config_desc = config_desc_buf,
      .config_desc_size = config_desc_buf_size,
      .config_hash = (uint8_t *)&conf_hash.digest[0],
      .config_hash_size = kHmacDigestNumBytes,
      .profile_name = CWT_PROFILE_NAME,
      .profile_name_size = kProfileNameLength};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_payload_build(
      &cwt_dice_chain_entry_payload_params, cdi1_entry_payload_buffer,
      &cdi1_entry_payload_size));

  // Try to generate DiceChainEntryInput, by reusing the cert buffer.
  size_t cdi1_entry_input_size = kCwtDiceChainEntryInputMaxVariableSizeBytes;
  if (cdi1_entry_input_size > *cert_size)
    return kErrorCertInvalidSize;
  cwt_dice_chain_entry_input_values_t cwt_dice_chain_entry_input_params = {
      .payload = cdi1_entry_payload_buffer,
      .payload_size = cdi1_entry_payload_size};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_input_build(
      &cwt_dice_chain_entry_input_params, cert, &cdi1_entry_input_size));

  // Obtain digest & sign
  hmac_digest_t tbs_digest;
  hmac_sha256(cert, cdi1_entry_input_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  util_p256_signature_le_to_be_convert(curr_tbs_signature.r,
                                       curr_tbs_signature.s);

  // Build the final DiceEntry
  cwt_dice_chain_entry_values_t cwt_dice_chain_entry_params = {
      .payload = cdi1_entry_payload_buffer,
      .payload_size = cdi1_entry_payload_size,
      .signature = (uint8_t *)&curr_tbs_signature,
      .signature_size = sizeof(ecdsa_p256_signature_t)};
  HARDENED_RETURN_IF_ERROR(cwt_dice_chain_entry_build(
      &cwt_dice_chain_entry_params, cert, cert_size));

  // Save the CDI_1 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
      *kDiceKeyCdi1.keymgr_diversifier));

  return kErrorOk;
}

static rom_error_t cose_key_check_valid(const uint8_t *cert, size_t cert_size,
                                        const ecdsa_p256_public_key_t *pubkey,
                                        hardened_bool_t *cert_valid_output) {
  if (cert_size < kDiceCwtCoseKeyMinSizeBytes) {
    return kErrorDiceCwtCoseKeyNotFound;
  }
  memcpy(&expected_cose_key_id[kDiceCwtCoseKeyIdHeaderSizeBytes], pubkey->y,
         sizeof(pubkey->y));
  cert += cert_size - kDiceCwtCoseKeyIdOffsetBytes - kDiceCwtCoseKeyIdSizeBytes;
  if (memcmp(cert, expected_cose_key_id, sizeof(expected_cose_key_id)) == 0) {
    *cert_valid_output = kHardenedBoolTrue;
  }
  return kErrorOk;
}

static rom_error_t cose_sign1_check_valid(const uint8_t *cert, size_t cert_size,
                                          const hmac_digest_t *pubkey_id,
                                          hardened_bool_t *cert_valid_output) {
  if (cert_size < kDiceCwtCoseSign1MinSizeBytes) {
    return kErrorDiceCwtCoseKeyNotFound;
  }
  fill_dice_id_string(
      (uint8_t *)(pubkey_id->digest),
      &expected_cose_sign1_id[kDiceCwtCoseSign1IdHeaderSizeBytes]);
  cert += kDiceCwtCoseSign1IdOffsetBytes;
  if (memcmp(cert, expected_cose_sign1_id, sizeof(expected_cose_sign1_id)) ==
      0) {
    *cert_valid_output = kHardenedBoolTrue;
  }
  return kErrorOk;
}

rom_error_t dice_cert_check_valid(const perso_tlv_cert_obj_t *cert_obj,
                                  const hmac_digest_t *pubkey_id,
                                  const ecdsa_p256_public_key_t *pubkey,
                                  hardened_bool_t *cert_valid_output) {
  *cert_valid_output = kHardenedBoolFalse;

  const size_t cert_size = cert_obj->cert_body_size;
  if (cert_size < kDiceCwtMagicSizeBytes) {
    return kErrorDiceCwtCoseKeyNotFound;
  }

  const uint8_t *cert = cert_obj->cert_body_p;

  if (*cert == kDiceCwtCoseKeyMagic) {
    return cose_key_check_valid(cert, cert_size, pubkey, cert_valid_output);
  } else if (*cert == kDiceCwtCoseSign1Magic) {
    return cose_sign1_check_valid(cert, cert_size, pubkey_id,
                                  cert_valid_output);
  }

  return kErrorDiceCwtCoseKeyNotFound;
}
