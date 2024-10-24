// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cbor.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "otp_ctrl_regs.h"  // Generated.

// Labels
#define CWT_COSE_KEY_LABEL_TYPE (1)
#define CWT_COSE_KEY_LABEL_ALG (3)
#define CWT_COSE_KEY_LABEL_CRUVE (-1)
#define CWT_COSE_KEY_LABEL_EC2_X (-2)
#define CWT_COSE_KEY_LABEL_EC2_Y (-3)
#define CWT_LABEL_ISS (1)
#define CWT_LABEL_SUB (2)
#define CWT_LABEL_CODE_HASH (-4670545)
#define CWT_LABEL_CFG_HASH (-4670547)
#define CWT_LABEL_CFG_DESCR (-4670548)
#define CWT_LABEL_AUTH_HASH (-4670549)
#define CWT_LABEL_MODE (-4670551)
#define CWT_LABEL_SUBJECT_PK (-4670552)
#define CWT_LABEL_KEY_USAGE (-4670553)
#define CWT_LABEL_PROFILE_NAME (-4670554)

// Values
#define CWT_COSE_KEY_ALG_ECDSA256 (-7)
#define CWT_COSE_EC2_CRUVE_P256 (1)
#define CWT_COSE_KEY_TYPE_EC2 (2)

#define CWT_PROFILE_NAME "android.16"
#define CWT_PROFILE_NAME_VALUE_LEN 10 /* "android.16" */
#define CWT_PROFILE_NAME_LEN (1 + CWT_PROFILE_NAME_VALUE_LEN)

#define CWT_ISSU_SUBJ_KEY_ID_LEN kHmacDigestNumBytes
#define CWT_ISSU_SUBJ_LEN (CWT_ISSU_SUBJ_KEY_ID_LEN * 2)

// Entry numbers
enum {
  kCoseKeyMapCount = 5,
  kDiceChainEntryArrayCount = 4,
  kDiceChainEntryInputArrayCount = 4,
  kDiceChainEntryPayloadMapCount = 10,
};

// CWT sizes
enum {
  kCoseKeyEcP256SizeBytes = 77,
  kCdi0MaxPayloadSizeBytes = 455,
};

// UDS (Creator) attestation key diverisfier constants.
// Note: versions are always set to 0 so these keys are always valid from the
// perspective of the keymgr hardware.
const sc_keymgr_diversification_t kUdsKeymgrDiversifier = {
    .salt =
        {
            0xabffa6a9,
            0xc781f1ad,
            0x4c1107ad,
            0xf9210d85,
            0x0931f555,
            0x6c5aef5d,
            0xb9ba4df0,
            0x77b248d2,
        },
    .version = 0,
};
// CDI_0 (OwnerIntermediate) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi0KeymgrDiversifier = {
    .salt =
        {
            0x3e5913c7,
            0x41156f1d,
            0x998ddb9f,
            0xfa334191,
            0x8a85380e,
            0xba76ca1a,
            0xdb17c4a7,
            0xfb8852dc,
        },
    .version = 0,
};
// CDI_1 (Owner) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi1KeymgrDiversifier = {
    .salt =
        {
            0x2d12c2e3,
            0x6acc6876,
            0x4bfb07ee,
            0xc45fc414,
            0x5d4fa9de,
            0xf295b128,
            0x50f49882,
            0xbbdefa29,
        },
    .version = 0,
};

const sc_keymgr_ecc_key_t kDiceKeyUds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldUdsKeySeedIdx,
    .keymgr_diversifier = &kUdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};
const sc_keymgr_ecc_key_t kDiceKeyCdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi0KeySeedIdx,
    .keymgr_diversifier = &kCdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};
const sc_keymgr_ecc_key_t kDiceKeyCdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi1KeySeedIdx,
    .keymgr_diversifier = &kCdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};

// PubKeyECDSA256 = {               ; COSE_Key [RFC9052 s7]
//     1 : 2,                       ; Key type : EC2
//     3 : AlgorithmES256,          ; Algorithm : ECDSA w/ SHA-256
//     -1 : 1,                      ; Curve: P256
//     -2 : bstr,                   ; X coordinate, big-endian
//     -3 : bstr                    ; Y coordinate, big-endian
// }
static rom_error_t cose_key_ec_p256_build(ecdsa_p256_public_key_t *uds_pubkey,
                                          uint8_t *cose_key_buffer,
                                          size_t *cose_key_buffer_size) {
  struct CborOut kCborOutHandle;
  struct CborOut *pCborOut = &kCborOutHandle;

  RETURN_IF_ERROR(
      cbor_write_out_init(pCborOut, cose_key_buffer, *cose_key_buffer_size));
  RETURN_IF_ERROR(cbor_map_init(pCborOut, kCoseKeyMapCount));
  RETURN_IF_ERROR(cbor_write_pair_uint_uint(pCborOut, CWT_COSE_KEY_LABEL_TYPE,
                                            CWT_COSE_KEY_TYPE_EC2));
  RETURN_IF_ERROR(cbor_write_pair_uint_int(pCborOut, CWT_COSE_KEY_LABEL_ALG,
                                           CWT_COSE_KEY_ALG_ECDSA256));
  RETURN_IF_ERROR(cbor_write_pair_int_uint(pCborOut, CWT_COSE_KEY_LABEL_CRUVE,
                                           CWT_COSE_EC2_CRUVE_P256));

  RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, CWT_COSE_KEY_LABEL_EC2_X,
                                            (uint8_t *)uds_pubkey->x,
                                            sizeof(uds_pubkey->x)));
  RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, CWT_COSE_KEY_LABEL_EC2_Y,
                                            (uint8_t *)uds_pubkey->y,
                                            sizeof(uds_pubkey->y)));
  *cose_key_buffer_size = CborOutSize(pCborOut);

  return kErrorOk;
}

rom_error_t dice_uds_tbs_cert_build(
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    cert_key_id_pair_t *key_ids, ecdsa_p256_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  HARDENED_RETURN_IF_ERROR(
      cose_key_ec_p256_build(uds_pubkey, tbs_cert, tbs_cert_size));
  return kErrorOk;
}

// protected:
// a1    # map(1)
//    01 #   unsigned(1)
//    26 #   negative(-7)
const uint8_t cbor_map_algo_es256[] = {0xa1, 0x01, 0x26};

// a0    # map(0)
const uint8_t cbor_map_0[] = {0xa0};

// a1             # map(1)
//    3a 00011174 #   negative(-70,005)
//    00          #   unsigned(0)
const uint8_t conf_desc_sec_ver_0[] = {0xa1, 0x3a, 0x00, 0x01,
                                       0x11, 0x74, 0x00};

static ecdsa_p256_signature_t curr_tbs_signature = {.r = {0}, .s = {0}};

/**
 * Helper function to convert an attestation certificate signature from little
 * to big endian.
 */
static void curr_tbs_signature_le_to_be_convert(ecdsa_p256_signature_t *sig) {
  util_reverse_bytes(sig->r, kEcdsaP256SignatureComponentBytes);
  util_reverse_bytes(sig->s, kEcdsaP256SignatureComponentBytes);
}

/**
 * Convert 32-byte digest to 64-byte string, with tailing "\0"
 */
static void fill_dice_id_string(const uint8_t dice_id[CWT_ISSU_SUBJ_KEY_ID_LEN],
                                char dice_id_str[CWT_ISSU_SUBJ_LEN + 1]) {
  size_t idx;
  for (idx = 0; idx < CWT_ISSU_SUBJ_KEY_ID_LEN; idx++, dice_id_str += 2)
    util_hexdump_byte(dice_id[idx], (uint8_t *)&dice_id_str[0]);
}

static rom_error_t dice_chain_entry_payload_build(
    uint8_t *payload, size_t *payload_size, const char *issuer,
    const size_t issuer_size, const char *subject, const size_t subject_size,
    uint8_t *cose_key, const size_t cose_key_size,
    hmac_digest_t *rom_ext_measurement) {
  if (*payload_size > kCdi0MaxPayloadSizeBytes)
    return kErrorCertInvalidSize;

  struct CborOut kCborOutHandle;
  struct CborOut *pCborOut = &kCborOutHandle;

  RETURN_IF_ERROR(cbor_write_out_init(pCborOut, payload, *payload_size));
  RETURN_IF_ERROR(cbor_map_init(pCborOut, kDiceChainEntryPayloadMapCount));
  RETURN_IF_ERROR(cbor_write_pair_uint_tstr(pCborOut, CWT_LABEL_ISS, issuer));
  RETURN_IF_ERROR(cbor_write_pair_uint_tstr(pCborOut, CWT_LABEL_SUB, subject));
  RETURN_IF_ERROR(cbor_write_pair_int_bytes(
      pCborOut, CWT_LABEL_CODE_HASH, (uint8_t *)&rom_ext_measurement->digest[0],
      kHmacDigestNumBytes));

  hmac_digest_t tbs_digest;
  hmac_sha256(conf_desc_sec_ver_0, sizeof(conf_desc_sec_ver_0), &tbs_digest);
  util_reverse_bytes(tbs_digest.digest, kHmacDigestNumBytes);
  RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, CWT_LABEL_CFG_HASH,
                                            (uint8_t *)&tbs_digest.digest[0],
                                            kHmacDigestNumBytes));
  RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, CWT_LABEL_CFG_DESCR,
                                            &conf_desc_sec_ver_0[0],
                                            sizeof(conf_desc_sec_ver_0)));

  hmac_sha256(cbor_map_0, sizeof(cbor_map_0), &tbs_digest);
  util_reverse_bytes(tbs_digest.digest, kHmacDigestNumBytes);
  RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, CWT_LABEL_AUTH_HASH,
                                            (uint8_t *)&tbs_digest.digest[0],
                                            kHmacDigestNumBytes));
  uint8_t mode = 1;
  RETURN_IF_ERROR(
      cbor_write_pair_int_bytes(pCborOut, CWT_LABEL_MODE, &mode, 1));
  RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, CWT_LABEL_SUBJECT_PK,
                                            cose_key, cose_key_size));
  uint8_t key_usage = 0x20;
  RETURN_IF_ERROR(
      cbor_write_pair_int_bytes(pCborOut, CWT_LABEL_KEY_USAGE, &key_usage, 1));

  RETURN_IF_ERROR(cbor_write_pair_int_tstr(pCborOut, CWT_LABEL_PROFILE_NAME,
                                           CWT_PROFILE_NAME));
  *payload_size = CborOutSize(pCborOut);

  return kErrorOk;
}

// DiceChainEntryInput = [
//  context: "Signature1",
//  protected: bstr .cbor { 1 : AlgorithmES256 },
//  external_aad: bstr .size 0,
//  payload: bstr .cbor DiceChainEntryPayload
// ]
static rom_error_t dice_chain_entry_input_build(
    uint8_t *dice_chain_entry_input_buffer,
    size_t *dice_chain_entry_input_buffer_size, uint8_t *cdi0_payload_buffer,
    const size_t cdi0_payload_size) {
  if (cdi0_payload_size > *dice_chain_entry_input_buffer_size)
    return kErrorCertInvalidSize;

  struct CborOut kCborOutHandle;
  struct CborOut *pCborOut = &kCborOutHandle;

  RETURN_IF_ERROR(cbor_write_out_init(pCborOut, dice_chain_entry_input_buffer,
                                      *dice_chain_entry_input_buffer_size));
  RETURN_IF_ERROR(cbor_array_init(pCborOut, kDiceChainEntryInputArrayCount));
  RETURN_IF_ERROR(cbor_write_string(pCborOut, "Signature1"));
  RETURN_IF_ERROR(cbor_write_bytes(pCborOut, (uint8_t *)&cbor_map_algo_es256[0],
                                   sizeof(cbor_map_algo_es256)));
  RETURN_IF_ERROR(cbor_write_bytes(pCborOut, NULL, 0));
  RETURN_IF_ERROR(
      cbor_write_bytes(pCborOut, cdi0_payload_buffer, cdi0_payload_size));
  *dice_chain_entry_input_buffer_size = CborOutSize(pCborOut);

  return kErrorOk;
}

// DiceChainEntry = [      ; COSE_Sign1 (untagged), [RFC9052 s4.2]
//     protected : bstr .cbor { 1 : AlgorithmES256},
//     unprotected: {},
//     payload: bstr .cbor DiceChainEntryPayload,
//     signature: bstr ; ECDSA(SigningKey, DiceChainEntryInput)
// ]
static rom_error_t dice_chain_build(
    uint8_t *cert, size_t *cert_size, uint8_t *cdi0_payload_buffer,
    const size_t payload_buff_size,
    ecdsa_p256_signature_t *curr_tbs_signature) {
  struct CborOut kCborOutHandle;
  struct CborOut *pCborOut = &kCborOutHandle;

  RETURN_IF_ERROR(cbor_write_out_init(pCborOut, cert, *cert_size));
  RETURN_IF_ERROR(cbor_array_init(pCborOut, kDiceChainEntryArrayCount));
  RETURN_IF_ERROR(cbor_write_bytes(pCborOut, (uint8_t *)&cbor_map_algo_es256[0],
                                   sizeof(cbor_map_algo_es256)));
  RETURN_IF_ERROR(cbor_map_init(pCborOut, 0));
  RETURN_IF_ERROR(cbor_write_bytes(pCborOut, (uint8_t *)&cdi0_payload_buffer[0],
                                   payload_buff_size));
  // (r+s) in RAW
  RETURN_IF_ERROR(cbor_write_bytes(pCborOut, (uint8_t *)curr_tbs_signature,
                                   sizeof(ecdsa_p256_signature_t)));
  *cert_size = CborOutSize(pCborOut);

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  size_t payload_buff_size = kCdi0MaxPayloadSizeBytes;
  uint8_t cdi0_payload_buffer[payload_buff_size];
  size_t cose_key_size = kCoseKeyEcP256SizeBytes;
  uint8_t cose_key_buffer[cose_key_size];
  /* NULL terminated string buffer */
  char issuer[CWT_ISSU_SUBJ_LEN + 1] = {0};
  char subject[CWT_ISSU_SUBJ_LEN + 1] = {0};

  HARDENED_RETURN_IF_ERROR(
      cose_key_ec_p256_build(cdi_0_pubkey, cose_key_buffer, &cose_key_size));

  // Try to generate DiceChainEntryPayload
  fill_dice_id_string((uint8_t *)(&key_ids->endorsement->digest[0]),
                      &issuer[0]);
  fill_dice_id_string((uint8_t *)(&key_ids->cert->digest[0]), &subject[0]);
  HARDENED_RETURN_IF_ERROR(dice_chain_entry_payload_build(
      cdi0_payload_buffer, &payload_buff_size, &issuer[0], sizeof(issuer),
      subject, sizeof(subject), cose_key_buffer, cose_key_size,
      rom_ext_measurement));

  // Try to generate DiceChainEntryInput, by reusing the cert buffer.
  size_t dice_chain_entry_input_size = *cert_size;
  HARDENED_RETURN_IF_ERROR(
      dice_chain_entry_input_build(cert, &dice_chain_entry_input_size,
                                   cdi0_payload_buffer, payload_buff_size));
  // Obtain digest & sign
  hmac_digest_t tbs_digest;
  hmac_sha256(cert, dice_chain_entry_input_size, &tbs_digest);
  HARDENED_RETURN_IF_ERROR(
      otbn_boot_attestation_endorse(&tbs_digest, &curr_tbs_signature));
  curr_tbs_signature_le_to_be_convert(&curr_tbs_signature);

  // Build the final DiceEntry
  HARDENED_RETURN_IF_ERROR(
      dice_chain_build(cert, cert_size, cdi0_payload_buffer, payload_buff_size,
                       &curr_tbs_signature));
  // Save the CDI_0 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
      *kDiceKeyCdi0.keymgr_diversifier));

  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  HARDENED_RETURN_IF_ERROR(
      dice_cdi_0_cert_build(owner_measurement, owner_security_version, key_ids,
                            cdi_1_pubkey, cert, cert_size));
  // Save the CDI_1 private key to OTBN DMEM so it can endorse the next stage.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
      *kDiceKeyCdi1.keymgr_diversifier));

  return kErrorOk;
}
