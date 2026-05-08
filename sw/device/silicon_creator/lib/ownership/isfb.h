// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_ISFB_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_ISFB_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/ownership/owner_block.h"

#ifdef __cplusplus
extern "C" {
#endif

enum {
  // The number of bits in the strike mask is fixed to 128. Each bit in the
  // strike mask corresponds to a `uint32_t` word.
  kIsfbExpectedStrikeBitCount = 128,
};

inline uint32_t isfb_expected_count_get(const manifest_ext_isfb_t *ext) {
  return ext->product_expr_count + kIsfbExpectedStrikeBitCount;
}

/**
 * Processes the Integrator Specific FW Binding (ISFB) boot request.
 *
 * This function processes the ISFB boot request and performs the necessary
 * checks to ensure that the firmware is bound to the correct
 * integrator-specific firmware binding configuration.
 *
 * The checks performed are:
 * - The ISFB extension is valid.
 * - The ISFB configuration is present in the owner configuration.
 * - The product expression count set in the manifest is within the bounds of
 * the owner configuration.
 * - The strike mask yields the expected number of strikes in the ISFB info
 * page.
 * - The product expressions in the ISFB info page match the expected values.
 *
 * @param ext The ISFB extension from the manifest.
 * @param owner_config The owner configuration.
 * @param[out] checks_performed_count The number of checks performed. This
 * should be equivalent to the number of strike bits and the number of product
 * expressions. Use this value in the consuming code as a way to harden the call
 * against fault injection.
 *
 * @return The result of the operation.
 */
rom_error_t isfb_boot_request_process(const manifest_ext_isfb_t *ext,
                                      const owner_config_t *owner_config,
                                      uint32_t *checks_performed_count);

/**
 * Gets the flash erase policy for the ISFB info page.
 *
 * This function checks the erase policy for the ISFB info page based on the
 * provided owner configuration, key domain, and manifest node lock status.
 *
 * @param owner_config The owner configuration.
 * @param key_domain The key domain associated with the active secure boot key.
 * @param manifest_is_node_locked Indicates whether the manifest is node locked.
 * @param ext_isfb_erase The ISFB erase policy extension from the manifest. May
 * be NULL.
 * @param[out] erase_en The erase enable flag. Set to kHardenedBoolTrue if
 *                      erasing the ISFB info page is allowed, otherwise
 *                      kHardenedBoolFalse.
 * @return The result of the operation.
 */
rom_error_t isfb_info_flash_erase_policy_get(
    owner_config_t *owner_config, uint32_t key_domain,
    hardened_bool_t manifest_is_node_locked,
    const manifest_ext_isfb_erase_t *ext_isfb_erase, hardened_bool_t *erase_en);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_OWNERSHIP_ISFB_H_
