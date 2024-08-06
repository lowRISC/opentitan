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

enum {
  /**
   * DICE attestation measurement sizes, comprised of a SHA256 digest.
   */
  kDiceMeasurementSizeInBits = 256,
  kDiceMeasurementSizeInBytes = kDiceMeasurementSizeInBits / 8,
};

/**
 * DICE ECC key descriptors.
 */
extern const sc_keymgr_ecc_key_t kDiceKeyUds;
extern const sc_keymgr_ecc_key_t kDiceKeyCdi0;
extern const sc_keymgr_ecc_key_t kDiceKeyCdi1;

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
rom_error_t dice_uds_tbs_cert_build(cert_key_id_pair_t *key_ids,
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

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_H_
