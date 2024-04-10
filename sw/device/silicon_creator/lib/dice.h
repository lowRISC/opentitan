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
   * Attestation measurement sizes, comprised of a SHA256 digest.
   */
  kAttestMeasurementSizeInBits = 256,
  kAttestMeasurementSizeInBytes = kAttestMeasurementSizeInBits / 8,
  kAttestMeasurementSizeIn32BitWords =
      kAttestMeasurementSizeInBytes / sizeof(uint32_t),

  /**
   * Certificate Key ID size.
   */
  kCertKeyIdSizeInBytes = 20,
};

/**
 * Generates the UDS attestation keypair and (unendorsed) X.509 certificate.
 *
 * Preconditions: keymgr has been initialized, and is ready to be cranked.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param[in,out] uds_pubkey_id Pointer to the UDS public key ID.
 * @param[out] cert Buffer to hold the generated UDS certificate.
 * @param[in,out] cert_size Size of the UDS certificate (input value is the size
 *                          of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_uds_cert_build(manuf_certgen_inputs_t *inputs,
                                hmac_digest_t *uds_pubkey_id, uint8_t *cert,
                                size_t *cert_size);

/**
 * Generates the CDI_0 attestation keypair and X.509 certificate.
 *
 * Preconditions: keymgr has been cranked to the `CreatorRootKey` stage.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param uds_pubkey_id Pointer to the UDS public key ID.
 * @param[in,out] cdi_0_pubkey_id Pointer to the CDI_0 public key ID.
 * @param[out] cert Buffer to hold the generated CDI_0 certificate.
 * @param[in,out] cert_size Size of the CDI_0 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cdi_0_cert_build(manuf_certgen_inputs_t *inputs,
                                  hmac_digest_t *uds_pubkey_id,
                                  hmac_digest_t *cdi_0_pubkey_id, uint8_t *cert,
                                  size_t *cert_size);

/**
 * Generates the CDI_1 attestation keypair and X.509 certificate.
 *
 * Preconditions: keymgr has been cranked to the `OwnerIntermediateKey` stage.
 *
 * @param inputs Pointer to the personalization input data payload.
 * @param cdi_0_pubkey_id Pointer the CDI_0 public key ID.
 * @param[out] cert Buffer to hold the generated CDI_1 certificate.
 * @param[in,out] cert_size Size of the CDI_1 certificate (input value is the
 *                          size of the allocated cert_buf, output value final
 *                          computed size of the certificate).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_cdi_1_cert_build(manuf_certgen_inputs_t *inputs,
                                  hmac_digest_t *cdi_0_pubkey_id, uint8_t *cert,
                                  size_t *cert_size);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DICE_H_
