// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TPM_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TPM_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"

/**
 * TPM ECC key descriptors.
 */
extern const sc_keymgr_ecc_key_t kTpmKeyEk;
extern const sc_keymgr_ecc_key_t kTpmKeyCek;
extern const sc_keymgr_ecc_key_t kTpmKeyCik;

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
rom_error_t tpm_ek_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *tpm_ek_pubkey,
                                  uint8_t *tbs_cert, size_t *tbs_cert_size);

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
rom_error_t tpm_cek_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                   ecdsa_p256_public_key_t *tpm_cek_pubkey,
                                   uint8_t *tbs_cert, size_t *tbs_cert_size);

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
rom_error_t tpm_cik_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                   ecdsa_p256_public_key_t *tpm_cik_pubkey,
                                   uint8_t *tbs_cert, size_t *tbs_cert_size);
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_TPM_H_
