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
 * Supported DICE attestation keys.
 */
typedef enum dice_key {
  kDiceKeyUds = 0,
  kDiceKeyCdi0 = 1,
  kDiceKeyCdi1 = 2,
} dice_key_t;

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
 * Generates the UDS attestation keypair and (unendorsed) X.509 certificate.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param uds_pubkey_id Pointer to the (current stage) UDS public key ID.
 * @param uds_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated UDS certificate.
 * @param[in,out] cert_size Size of the UDS certificate (input value is the size
 *                          of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_uds_cert_build(manuf_certgen_inputs_t *inputs,
                                hmac_digest_t *uds_pubkey_id,
                                attestation_public_key_t *uds_pubkey,
                                uint8_t *cert, size_t *cert_size);

/**
 * Generates the CDI_0 attestation keypair and X.509 certificate.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param uds_pubkey_id Pointer to the (previous stage) UDS public key ID.
 * @param cdi_0_pubkey_id Pointer to the (current stage) CDI_0 public key ID.
 * @param cdi_0_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated CDI_0 certificate.
 * @param[in,out] cert_size Size of the CDI_0 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cdi_0_cert_build(manuf_certgen_inputs_t *inputs,
                                  hmac_digest_t *uds_pubkey_id,
                                  hmac_digest_t *cdi_0_pubkey_id,
                                  attestation_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size);

/**
 * Generates the CDI_1 attestation keypair and X.509 certificate.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param cdi_0_pubkey_id Pointer to the (previous stage) CDI_0 public key ID.
 * @param cdi_1_pubkey_id Pointer to the (current stage) CDI_1 public key ID.
 * @param cdi_1_pubkey Pointer to the (current stage) public key in big endian.
 * @param[out] cert Buffer to hold the generated CDI_1 certificate.
 * @param[in,out] cert_size Size of the CDI_1 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cdi_1_cert_build(manuf_certgen_inputs_t *inputs,
                                  hmac_digest_t *cdi_0_pubkey_id,
                                  hmac_digest_t *cdi_1_pubkey_id,
                                  attestation_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_
