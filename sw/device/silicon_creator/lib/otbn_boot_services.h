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
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
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
 * @param additional_seed_idx The attestation key generation seed index to load.
 *                            The index corresponds to the seed offset in flash
 *                            info page `kFlashCtrlInfoPageAttestationKeySeeds`.
 * @param key_type Keymgr key type to generate, attestation or sealing.
 * @param diversification Salt and version information for key manager.
 * @param[out] public_key Attestation public key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_keygen(
    uint32_t additional_seed_idx, sc_keymgr_key_type_t key_type,
    sc_keymgr_diversification_t diversification,
    ecdsa_p256_public_key_t *public_key);

/**
 * Generate a deterministic ECC P256 attestation public key from a
 * keymgr-derived secret.
 *
 * This routine may be used to generate DICE attestation keys, TPM identity
 * keys, or any other deterministic asymmetric ECC P256 keys required. DICE keys
 * should be contructed from the "attestation" keymgr key type, while TPM keys
 * should be constructed form the "sealing" key type. The former are bound to
 * firmware updates, and change when ROM_EXT or Owner firmware is updated. The
 * latter remain stable across the lifetime of an ownership of the chip.
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
 * @param additional_seed_idx The attestation key generation seed index to load.
 *                            The index corresponds to the seed offset in flash
 *                            info page `kFlashCtrlInfoPageAttestationKeySeeds`.
 * @param key_type Keymgr key type to generate, attestation or sealing.
 * @param diversification Salt and version information for key manager.
 * @param[out] public_key Attestation public key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_attestation_keygen(
    uint32_t additional_seed_idx, sc_keymgr_key_type_t key_type,
    sc_keymgr_diversification_t diversification,
    ecdsa_p256_public_key_t *public_key);

/**
 * Wrapper for `otbn_boot_attestation_keygen()` that generates an ECC P256
 * keypair to build a certificate around, using Keymgr and OTBN, returning the
 * public key (in big endian order for inserting into a cert) and a key ID
 * (which is a SHA256 digest of the public key).
 *
 * Preconditions: keymgr has been initialized and cranked to the desired stage.
 *
 * @param key The description of the desired key to generate.
 * @param[out] pubkey_id The public key ID (for embedding into certificates).
 * @param[out] pubkey The public key.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_cert_ecc_p256_keygen(sc_keymgr_ecc_key_t key,
                                           hmac_digest_t *pubkey_id,
                                           ecdsa_p256_public_key_t *pubkey);

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
    uint32_t additional_seed, sc_keymgr_key_type_t key_type,
    sc_keymgr_diversification_t diversification);

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
                                          ecdsa_p256_signature_t *sig);

/**
 * Computes an ECDSA-P256 signature verification on OTBN.
 *
 * May be used for code signatures as well as attestation signatures. Returns
 * the recovered `r` value in `result`. The signature is valid if this `r`
 * value matches the `r` component of the signature, but the caller is
 * responsible for the final comparison.
 *
 * Expects the OTBN boot-services program to already be loaded; see
 * `otbn_boot_app_load`.
 *
 * @param key An ECDSA-P256 public key.
 * @param sig An ECDSA-P256 signature.
 * @param digest Message digest to check against.
 * @param[out] recovered_r Buffer for the recovered `r` value.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t otbn_boot_sigverify(const ecdsa_p256_public_key_t *key,
                                const ecdsa_p256_signature_t *sig,
                                const hmac_digest_t *digest,
                                uint32_t *recovered_r);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_
