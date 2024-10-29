// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

enum {
  /**
   * DICE attestation measurement sizes, comprised of a SHA256 digest.
   */
  kDiceMeasurementSizeInBits = 256,
  kDiceMeasurementSizeInBytes = kDiceMeasurementSizeInBits / 8,
};

extern const dice_cert_format_t kDiceCertFormat;
/**
 * DICE ECC key descriptors.
 */
extern const sc_keymgr_ecc_key_t kDiceKeyUds;
extern const sc_keymgr_ecc_key_t kDiceKeyCdi0;
extern const sc_keymgr_ecc_key_t kDiceKeyCdi1;

/**
 * Generates the UDS attestation keypair and (unendorsed) X.509 TBS certificate.
 *
 * @param otp_creator_sw_cfg_measurement Pointer to the CreatorSwCfg
 * measurement.
 * @param otp_owner_sw_cfg_measurement Pointer to the OwnerSwCfg measurement.
 * @param otp_rot_creator_auth_codesign_measurement Pointer to the
 * RotCreatorAuthCodesign measurement.
 * @param otp_rot_creator_auth_state_measurement Pointer to the
 * RotCreatorAuthState measurement.
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param uds_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated UDS certificate.
 * @param[in,out] cert_size Size of the UDS certificate (input value is the size
 *                          of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_uds_tbs_cert_build(
    hmac_digest_t *otp_creator_sw_cfg_measurement,
    hmac_digest_t *otp_owner_sw_cfg_measurement,
    hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    hmac_digest_t *otp_rot_creator_auth_state_measurement,
    cert_key_id_pair_t *key_ids, ecdsa_p256_public_key_t *uds_pubkey,
    uint8_t *tbs_cert, size_t *tbs_cert_size);

/**
 * Generates the CDI_0 attestation keypair and X.509 certificate.
 *
 * @param rom_ext_measurement Pointer to the ROM_EXT measurement.
 * @param rom_ext_security_version ROM_EXT security version.
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param cdi_0_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated CDI_0 certificate.
 * @param[in,out] cert_size Size of the CDI_0 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size);

/**
 * Generates the CDI_1 attestation keypair and X.509 certificate.
 *
 * @param owner_measurement Pointer to the owner firmware measurement.
 * @param owner_manifest_measurement Pointer to the owner manifest measurement.
 * @param owner_security_version Owner firmware security version.
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param cdi_1_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated CDI_1 certificate.
 * @param[in,out] cert_size Size of the CDI_1 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size);

/**
 * Check if a subject pubkey ID (serial number) or subject pubkey match the
 * contents of the provided certificate.
 *
 * @param cert_obj Pointer to the TLV cert object from the flash.
 * @param pubkey_id Pointer to the subject pubkey ID (serial number).
 * @param pubkey Pointer to the subject pubkey contents.
 * @param[out] cert_valid_output If unmatched, set `cert_valid_output` to
 * kHardenedBoolFalse for triggering cert regeneration.
 * @return errors encountered during the check.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cert_check_valid(const perso_tlv_cert_obj_t *cert_obj,
                                  const hmac_digest_t *pubkey_id,
                                  const ecdsa_p256_public_key_t *pubkey,
                                  hardened_bool_t *cert_valid_output);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_H_
