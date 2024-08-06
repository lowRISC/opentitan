// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_

#include <stdint.h>

#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"

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
 * DICE keyladder key descriptor.
 */
typedef struct dice_key {
  /**
   * Keymgr key type, either: attestation or sealing.
   *
   * Attestation keys are derived from keymgr state that changes when ROM_EXT or
   * Owner firmware is updated, while Sealing keys remain stable as long as a
   * device remains under the same ownership and hardware lifecycle state.
   */
  sc_keymgr_key_type_t type;
  /**
   * Index into the kFlashCtrlInfoPageAttestationKeySeeds flash info page that
   * holds a seed for generating the ECC key pair.
   */
  uint32_t keygen_seed_idx;
  /**
   * Pointer to the keymgr diversifier that is used when actuating the keymgr's
   * "output-generate" function to generate another ECC keygen seed that will be
   * sideloaded to OTBN.
   */
  const sc_keymgr_diversification_t *keymgr_diversifier;
  /**
   * Pointer to the keymgr diversifier that is used when actuating the keymgr's
   */
  sc_keymgr_state_t required_keymgr_state;
} dice_key_t;

extern const dice_key_t kDiceKeyUds;
extern const dice_key_t kDiceKeyCdi0;
extern const dice_key_t kDiceKeyCdi1;
extern const dice_key_t kDiceKeyTpmEk;
extern const dice_key_t kDiceKeyTpmCek;
extern const dice_key_t kDiceKeyTpmCik;

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
 * Generates the requested attestation ECC P256 keypair, returning the public
 * key and a key ID (which is a SHA256 digest of the public key).
 *
 * Preconditions: keymgr has been initialized and cranked to the desired stage.
 *
 * @param desired_key The desired key to generate.
 * @param[out] pubkey_id The public key ID (for embedding into certificates).
 * @param[out] pubkey The public key.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_attestation_keygen(dice_key_t key, hmac_digest_t *pubkey_id,
                                    ecdsa_p256_public_key_t *pubkey);

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
                                    ecdsa_p256_public_key_t *uds_pubkey,
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
                                  dice_cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size);

/**
 * Generates an X.509 TBS section of a TPM EK certificate.
 *
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param tpm_ek_pubkey Pointer to the TPM EK public key in big endian.
 * @param[out] tbs_cert Buffer to hold the generated TBS section.
 * @param[in,out] tbs_cert_size Size of the generated TBS section (input value
 *                              is the size of the allocated cert_buf, output
 *                              value final computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_tpm_ek_tbs_cert_build(dice_cert_key_id_pair_t *key_ids,
                                       ecdsa_p256_public_key_t *tpm_ek_pubkey,
                                       uint8_t *tbs_cert,
                                       size_t *tbs_cert_size);

/**
 * Generates an X.509 TBS section of a TPM CEK certificate.
 *
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param tpm_cek_pubkey Pointer to the TPM CEK public key in big endian.
 * @param[out] tbs_cert Buffer to hold the generated UDS section.
 * @param[in,out] tbs_cert_size Size of the generated TBS section (input value
 *                              is the size of the allocated cert_buf, output
 *                              value final computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_tpm_cek_tbs_cert_build(dice_cert_key_id_pair_t *key_ids,
                                        ecdsa_p256_public_key_t *tpm_cek_pubkey,
                                        uint8_t *tbs_cert,
                                        size_t *tbs_cert_size);

/**
 * Generates an X.509 TBS section of a TPM CIK certificate.
 *
 * @param key_ids Pointer to the (current and endorsement) public key IDs.
 * @param tpm_cik_pubkey Pointer to the TPM CIK public key in big endian.
 * @param[out] tbs_cert Buffer to hold the generated UDS section.
 * @param[in,out] tbs_cert_size Size of the generated TBS section (input value
 *                              is the size of the allocated cert_buf, output
 *                              value final computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_tpm_cik_tbs_cert_build(dice_cert_key_id_pair_t *key_ids,
                                        ecdsa_p256_public_key_t *tpm_cik_pubkey,
                                        uint8_t *tbs_cert,
                                        size_t *tbs_cert_size);
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_
