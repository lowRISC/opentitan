// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_

#include <stdint.h>

#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"

enum {
  /**
   * DICE attestation measurement sizes, comprised of a SHA256 digest.
   */
  kDiceMeasurementSizeInBits = 256,
  kDiceMeasurementSizeInBytes = kDiceMeasurementSizeInBits / 8,

  /**
   * DICE key ID size (for use in DICE certificates).
   */
  kDiceCertKeyIdSizeInBytes = 20,
};

/**
 * Supported DICE/TPM attestation keys.
 */
typedef enum dice_key {
  /**
   * DICE UDS key.
   */
  kDiceKeyUds = 0,
  /**
   * DICE CDI0 key.
   */
  kDiceKeyCdi0 = 1,
  /**
   * DICE CDI1 key.
   */
  kDiceKeyCdi1 = 2,
  /**
   * TPM EK key.
   */
  kDiceKeyTpmEk = 3,
  /**
   * TPM CEK key.
   */
  kDiceKeyTpmCek = 4,
  /**
   * TPM CIK key.
   */
  kDiceKeyTpmCik = 5,
} dice_key_t;

/**
 * A set of public key IDs required to generate an X.509 certificate.
 */
typedef struct dice_cert_key_id_pair {
  /**
   * Pointer to SHA256 digest of the public key matching the private key used to
   * endorse the certificate.
   */
  hmac_digest_t *endorsement;
  /**
   * Pointer to SHA256 digest of the public key the certificate is created for.
   */
  hmac_digest_t *cert;
} dice_cert_key_id_pair_t;

/**
 * Generates the requested attestation ECC keypair, returning the public key and
 * a key ID (which is a SHA256 digest of the public key).
 *
 * Preconditions: keymgr has been initialized and cranked to the desired stage.
 *
 * @param desired_key The desired attestation key to generate.
 * @param[out] pubkey_id The public key ID (for embedding into certificates).
 * @param[out] pubkey The public key.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_attestation_keygen(dice_key_t desired_key,
                                    hmac_digest_t *pubkey_id,
                                    attestation_public_key_t *pubkey);

/**
 * Generates the UDS attestation keypair and (unendorsed) X.509 TBS certificate.
 *
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param uds_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated UDS certificate.
 * @param[in,out] cert_size Size of the UDS certificate (input value is the size
 *                          of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_uds_tbs_cert_build(dice_cert_key_id_pair_t *key_ids,
                                    attestation_public_key_t *uds_pubkey,
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
                                  dice_cert_key_id_pair_t *key_ids,
                                  attestation_public_key_t *cdi_0_pubkey,
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
                                  dice_cert_key_id_pair_t *key_ids,
                                  attestation_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size);

/**
 * Generates an X.509 TBS section of a TPM EK certificate.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param tpm_ek_pubkey Pointer to the public key in big endian.
 * @param pubkey_id Pointer to the public key ID.
 * @param[out] tbs_cert Buffer to hold the generated TBS section.
 * @param[in,out] tbs_cert_size Size of the generated TBS section (input value
 *                              is the size of the allocated cert_buf, output
 *                              value final computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_tpm_ek_cert_build(manuf_certgen_inputs_t *inputs,
                                   attestation_public_key_t *tpm_ek_pubkey,
                                   hmac_digest_t *pubkey_id, uint8_t *tbs_cert,
                                   size_t *tbs_cert_size);

/**
 * Generates an X.509 TBS section of a TPM CEK certificate.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param tpm_cek_pubkey Pointer to the public key in big endian.
 * @param pubkey_id Pointer to the public key ID.
 * @param[out] tbs_cert Buffer to hold the generated UDS section.
 * @param[in,out] tbs_cert_size Size of the generated TBS section (input value
 *                              is the size of the allocated cert_buf, output
 *                              value final computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_tpm_cek_cert_build(manuf_certgen_inputs_t *inputs,
                                    attestation_public_key_t *tpm_cek_pubkey,
                                    hmac_digest_t *pubkey_id, uint8_t *tbs_cert,
                                    size_t *tbs_cert_size);

/**
 * Generates an X.509 TBS section of a TPM CIK certificate.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param tpm_cik_pubkey Pointer to the public key in big endian.
 * @param pubkey_id Pointer to the public key ID.
 * @param[out] tbs_cert Buffer to hold the generated UDS section.
 * @param[in,out] tbs_cert_size Size of the generated TBS section (input value
 *                              is the size of the allocated cert_buf, output
 *                              value final computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_tpm_cik_cert_build(manuf_certgen_inputs_t *inputs,
                                    attestation_public_key_t *tpm_cik_pubkey,
                                    hmac_digest_t *pubkey_id, uint8_t *tbs_cert,
                                    size_t *tbs_cert_size);
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_
