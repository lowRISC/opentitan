// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Loads the OTBN boot-services application.
 *
 * Loads the OTBN program that runs attestation and code-signature
 * verification. The program can later be cleared by wiping OTBN's IMEM and
 * DMEM, or by loading a diffierent OTBN application.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_app_load(void);

/**
 * OTBN attestation key types (DICE or TPM).
 */
typedef enum otbn_boot_attestation_key_type {
  kOtbnBootAttestationKeyTypeDice = kKeymgrKeyTypeAttestation,
  kOtbnBootAttestationKeyTypeTpm = kKeymgrKeyTypeSealing,
} otbn_boot_attestation_key_type_t;

/**
 * Generate an attestation public key from a keymgr-derived secret.
 *
 * This routine triggers the key manager to sideload key material into OTBN,
 * and also loads in an extra seed to XOR with the key material. The final
 * private key is:
 *   d = (additional_seed ^ keymgr_seed) mod n
 * ...where n is the P256 curve order. The public key is d*G, where G is the
 * P256 base point.
 *
 * The extra seed is expected to be the output from a specially seeded DRBG, and
 * is provisioned into flash at manufacturing time. It must be fully independent
 * from the key manager seed.
 *
 * Expects the OTBN boot-services program to already be loaded; see
 * `otbn_boot_app_load`.
 *
 * @param additional_seed The attestation key generation seed to load.
 * @param key_type OTBN attestation key type to generate. "DICE" attestation
 *                 keys are based on "attestation" keys from the keymgr; "TPM"
 *                 attestation keys are based on "sealing keys from the keymgr.
 * @param diversification Salt and version information for key manager.
 * @param[out] public_key Attestation public key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_keygen(
    attestation_key_seed_t additional_seed,
    otbn_boot_attestation_key_type_t key_type,
    keymgr_diversification_t diversification,
    attestation_public_key_t *public_key);

/**
 * Saves an attestation private key to OTBN's scratchpad.
 *
 * This routine takes the same arguments as `otbn_boot_attestation_keygen`, but
 * instead of computing the public key, it computes only the private key and
 * saves it to OTBN's scratchpad memory.
 *
 * Expects the OTBN boot-services program to already be loaded; see
 * `otbn_boot_app_load`.
 *
 * @param additional_seed The attestation key generation seed to load.
 * @param key_type OTBN attestation key type to generate. "DICE" attestation
 *                 keys are based on "attestation" keys from the keymgr; "TPM"
 *                 attestation keys are based on "sealing keys from the keymgr.
 * @param diversification Salt and version information for key manager.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_key_save(
    attestation_key_seed_t additional_seed,
    otbn_boot_attestation_key_type_t key_type,
    keymgr_diversification_t diversification);

/**
 * Clears any saved attestation key from OTBN's scratchpad.
 *
 * This routine clears OTBN's DMEM. If called after
 * `otbn_boot_attestation_key_save`, it will clear the saved key.
 *
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_key_clear(void);

/**
 * Signs the message with the saved attestation key, and clears the key.
 *
 * Must be called when there is a saved attestation key in OTBN's scratchpad;
 * use `otbn_boot_attestation_key_save` to store one.
 *
 * The intended purpose of this function is to sign the current stage's
 * attestation certificate with the private key of the previous stage. The
 * caller should hash the certificate with SHA-256 before calling this
 * function.
 *
 * Note that the digest gets interpreted by OTBN in little-endian order. If the
 * HMAC block has not been set to produce little-endian digests, then the
 * digest bytes should be reversed before they are passed here.
 *
 * Expects the OTBN boot-services program to already be loaded; see
 * `otbn_boot_app_load`.
 *
 * @param digest Digest to sign.
 * @param[out] sig Resulting signature.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_endorse(const hmac_digest_t *digest,
                                          attestation_signature_t *sig);

/**
 * Computes the modular exponentiation of an RSA signature on OTBN.
 *
 * Given an RSA public key and sig, this function computes sig^e mod n using
 * Montgomery multiplication, where
 * - sig is an RSA signature,
 * - e and n are the exponent and the modulus of the key, respectively.
 *
 * The key exponent is always 65537; no other exponents are supported.
 *
 * Expects the OTBN boot-services program to already be loaded; see
 * `otbn_boot_app_load`.
 *
 * @param key An RSA public key.
 * @param sig Buffer that holds the signature, little-endian.
 * @param[out] result Buffer to write the result to, little-endian.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_sigverify_mod_exp(const sigverify_rsa_key_t *key,
                                        const sigverify_rsa_buffer_t *sig,
                                        sigverify_rsa_buffer_t *result);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_
