// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_CHAIN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_CHAIN_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/datatypes.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initialize the dice chain builder with data from the flash pages.
 *
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_init(void);

/**
 * Prepare the UDS key and check the UDS certificate.
 *
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_attestation_silicon(void);

/**
 * Check the CDI_0 certificate and regenerate if invalid.
 *
 * @param rom_ext_measurement Pointer to the measurements to attest.
 * @param rom_ext_manifest Pointer to the current rom_ext manifest.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_attestation_creator(
    keymgr_binding_value_t *rom_ext_measurement,
    const manifest_t *rom_ext_manifest);

/**
 * Check the CDI_1 certificate and regenerate if invalid.
 *
 * @param owner_manifest Pointer to the owner SW manifest to be boot.
 * @param bl0_measurement Pointer to the measurement of the owner firmware.
 * @param owner_measurement Pointer to the measurement of the owner config.
 * @param sealing_binding Pointer to the owner's sealing diversification
 *        constant.
 * @param key_domain Domain of the Owner SW signing key.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_attestation_owner(
    const manifest_t *owner_manifest, keymgr_binding_value_t *bl0_measurement,
    hmac_digest_t *owner_measurement, keymgr_binding_value_t *sealing_binding,
    owner_app_domain_t key_domain);

/**
 * Write back the certificate chain to flash if changed.
 *
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_flush_flash(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_DICE_CHAIN_H_
