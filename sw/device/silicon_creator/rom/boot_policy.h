// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_H_

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Type alias for the ROM_EXT entry point.
 *
 * The entry point address obtained from the ROM_EXT manifest must be cast to a
 * pointer to this type before being called.
 */
typedef void rom_ext_entry_point(void);

/**
 * Object which captures which slot (A or B) of the ROM_EXT firmware must
 * be tried first for booting. The order is decided based on the security
 * versions in the images' manifests.
 *
 * ROM_EXT images must be verified prior to handing over execution. A slot
 * with lower priority may be chosen if the other one fails verification.
 */
typedef struct boot_policy {
  /**
   * The first ROM_EXT image to boot according to the policy.
   *
   * This is either kBootSlotA or kBootSlotB.
   */
  boot_slot_t first_choice;
} boot_policy_t;

/**
 * Following the boot policy, choose the boot order for the ROM_EXT manifests.
 *
 * Work out the boot order for the ROM_EXT images according to the security
 * versions in their manifests.
 *
 * The chosen ROM_EXT image must be verified prior to handing over execution.
 *
 * @param boot_policy the boot order for the ROM_EXT manifests is written here.
 * @return The success/error state of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_policy_choose_slot(boot_policy_t *boot_policy);

/**
 * Get the preferred ROM_EXT image to boot.
 *
 * @return Either kBootSlotA or kBootSlotB.
 */
OT_WARN_UNUSED_RESULT
static inline boot_slot_t boot_policy_get_first_choice(boot_policy_t policy) {
  return policy.first_choice;
}

/**
 * Get the ROM_EXT image to boot if the preferred image fails verification.
 *
 * @return Either kBootSlotA or kBootSlotB.
 */
OT_WARN_UNUSED_RESULT
static inline boot_slot_t boot_policy_get_second_choice(boot_policy_t policy) {
  return (boot_slot_t)(policy.first_choice ^ (kBootSlotA ^ kBootSlotB));
}

/**
 * Load the given image, if necessary, and return a pointer to it.
 *
 * @param boot_slot Either kBootSlotA or kBootSlotB. Identifies which image
 *   should be loaded. In some tops images are mapped in memory and this
 *   function may limit itself to return their location in memory.
 * @return Pointer to the image in memory or @c NULL in case of failures.
 */
OT_WARN_UNUSED_RESULT
const void *boot_policy_load_image(boot_slot_t boot_slot);

/**
 * Get the pointer to a loaded image.
 *
 * @param boot_slot Either kBootSlotA or kBootSlotB.
 * @return The pointer to the image specified in @p boot_slot. If the specified
 *   image has not been loaded with boot_policy_load_image(), this function
 *   may return NULL. Alternatively, in tops where images are mapped in memory,
 *   the image pointer is always returned, independently of whether the image
 *   was loaded or not beforehand.
 */
OT_WARN_UNUSED_RESULT
const void *boot_policy_get_image(boot_slot_t boot_slot);

/**
 * Notify that an image is no longer needed and can be unloaded.
 *
 * This function is used to notify the NVM subsystem that a ROM_EXT image is
 * no longer needed and can be unloaded from memory.
 *
 * @param boot_slot Either kBootSlotA or kBootSlotB. Identifies which image
 *   should be unloaded. In some tops images are mapped in memory and this
 *   function may be a no-op.
 */
void boot_policy_unload_image(boot_slot_t boot_slot);

/**
 * Checks the fields of a ROM_EXT manifest.
 *
 * This function performs bounds checks on the fields of the manifest, checks
 * that its `identifier` is correct, and its `security_version` is greater than
 * or equal to the minimum required security version.
 *
 * @param manifest A ROM_EXT manifest.
 * @param boot_data Boot data.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_policy_manifest_check(const manifest_t *manifest,
                                       const boot_data_t *boot_data);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_BOOT_POLICY_H_
