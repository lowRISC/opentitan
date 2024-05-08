// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_
#define OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/lib/sw/device/silicon_creator/attestation.h"

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
rom_error_t otbn_boot_sigverify(const attestation_public_key_t *key,
                                const attestation_signature_t *sig,
                                const hmac_digest_t *digest,
                                uint32_t *recovered_r);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_LIB_SW_DEVICE_SILICON_CREATOR_LIB_OTBN_BOOT_SERVICES_H_
