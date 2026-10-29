// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_MLDSA_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_MLDSA_H_
#include <stdalign.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/sigverify/mldsa_key.h"

enum {
  // Shared scratch buffer size to use for ML-DSA operations
  kDiceMldsaRomExtAttestationScratchBufferSize = 32 * 1024,
  kDiceMldsaPersoScratchBufferSize = 24 * 1024,
};

typedef struct attest_params attest_params_t;

/**
 * Attests the next-stage CDI certificates.
 *
 * Switches to `params->scratch_buf` as the stack before calling
 * `dice_attest_next_cdi_impl`, and shreds the stack buffer before returning.
 *
 * @param params Parameters for the attestation.
 * @param sealing_binding Keymgr sealing binding value.
 * @param max_key_version Maximum key version allowed for key derivation.
 * @param exts Pointer to the private extensions DER buffer.
 * @param exts_size Size of the private extensions DER buffer.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_attest_next_cdi(const attest_params_t *params,
                                 const keymgr_binding_value_t *sealing_binding,
                                 uint32_t max_key_version, const uint8_t *exts,
                                 size_t exts_size);

// `key_ids->endorsement` must already be populated
OT_WARN_UNUSED_RESULT
rom_error_t dice_uds_mldsa_tbs_cert_generate_and_build(
    const hmac_digest_t *otp_creator_sw_cfg_measurement,
    const hmac_digest_t *otp_owner_sw_cfg_measurement,
    const hmac_digest_t *otp_rot_creator_auth_codesign_measurement,
    const hmac_digest_t *otp_rot_creator_auth_state_measurement,
    const cert_key_id_pair_t *key_ids, mldsa_parameter_set_t mldsa_params_set,
    uint8_t *tbs_cert_buffer, size_t *tbs_cert_size);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_MLDSA_H_
