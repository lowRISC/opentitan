// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest_size.h"
// FIXME: Move sigverify to sw/device/silicon_creator/lib
#include "sw/device/silicon_creator/mask_rom/sig_verify_keys.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Manifest for boot stage images stored in flash.
 *
 * OpenTitan secure boot, at a minimum, consists of four boot stages: ROM,
 * ROM_EXT, BL0, and Kernel. ROM is stored in the read-only Mask ROM while
 * remaning stages are stored in flash. This structure must be placed at the
 * beginning of ROM_EXT and BL0 images so that ROM and ROM_EXT can verify
 * integrity and authenticity of the next stage before handing over execution.
 *
 * Use of this struct for stages following BL0 is optional.
 *
 * Note: The definitions in
 * sw/host/rom_ext_image_tools/signer/image/src/manifest.rs must be updated if
 * this struct is modified. Please see the instructions in that file.
 */
typedef struct manifest {
  /**
   * Manifest identifier.
   */
  uint32_t identifier;
  /**
   * FIXME: remove this field.
   */
  uint32_t reserved0;
  /**
   * Image signature.
   *
   * The signed region of an image starts at `image_length` and ends at the
   * end of the image. The start and the length of the signed region can be
   * obtained using `manifest_signed_region_get`.
   */
  sigverify_rsa_buffer_t signature;
  /**
   * Image length in bytes.
   */
  uint32_t image_length;
  /**
   * FIXME: Replace with max_version, min_version.
   */
  uint32_t image_version;
  /**
   * Image timestamp.
   */
  uint64_t image_timestamp;
  /**
   * Exponent of the signer's RSA public key.
   */
  uint32_t exponent;
  /**
   * FIXME: remove this field.
   */
  uint32_t reserved1;
  /**
   * FIXME: Replace these with binding_tag and max_key_version.
   */
  uint32_t usage_constraints[8];
  uint32_t lockdown_info[4];
  /**
   * Modulus of the signer's RSA public key.
   */
  sigverify_rsa_buffer_t modulus;
  /**
   * Extension fields.
   * FIXME: Remove these until we have a clear use-case.
   */
  uint32_t extension0_offset;
  uint32_t extension0_checksum;
  uint32_t extension1_offset;
  uint32_t extension1_checksum;
  uint32_t extension2_offset;
  uint32_t extension2_checksum;
  uint32_t extension3_offset;
  uint32_t extension3_checksum;
} manifest_t;

OT_ASSERT_MEMBER_OFFSET(manifest_t, identifier, 0);
OT_ASSERT_MEMBER_OFFSET(manifest_t, reserved0, 4);
OT_ASSERT_MEMBER_OFFSET(manifest_t, signature, 8);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_length, 392);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_version, 396);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_timestamp, 400);
OT_ASSERT_MEMBER_OFFSET(manifest_t, exponent, 408);
OT_ASSERT_MEMBER_OFFSET(manifest_t, reserved1, 412);
OT_ASSERT_MEMBER_OFFSET(manifest_t, usage_constraints, 416);
OT_ASSERT_MEMBER_OFFSET(manifest_t, lockdown_info, 448);
OT_ASSERT_MEMBER_OFFSET(manifest_t, modulus, 464);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension0_offset, 848);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension0_checksum, 852);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension1_offset, 856);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension1_checksum, 860);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension2_offset, 864);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension2_checksum, 868);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension3_offset, 872);
OT_ASSERT_MEMBER_OFFSET(manifest_t, extension3_checksum, 876);
OT_ASSERT_SIZE(manifest_t, MANIFEST_SIZE);

/**
 * Signed region of an image.
 */
typedef struct manifest_signed_region {
  /**
   * Start of the signed region of an image.
   */
  const void *start;
  /**
   * Length of the signed region of an image in bytes.
   */
  size_t length;
} manifest_signed_region_t;

/**
 * Allowed bounds for the `image_length` field.
 */
enum {
  // FIXME: Update min value after we have a fairly representative ROM_EXT.
  kManifestImageLengthMin = sizeof(manifest_t),
  kManifestImageLengthMax = 64 * 1024,
};

/**
 * Gets the signed region of an image.
 *
 * This function also performs a basic check to ensure that the length of the
 * image is within a reasonable range.
 *
 * @param manifest A manifest
 * @param[out] signed_region Signed region of an image.
 * @return The result of the operation.
 */
inline rom_error_t manifest_signed_region_get(
    const manifest_t *manifest, manifest_signed_region_t *signed_region) {
  if (manifest->image_length < kManifestImageLengthMin ||
      manifest->image_length > kManifestImageLengthMax) {
    return kErrorManifestInternal;
  }
  *signed_region = (manifest_signed_region_t){
      .start = &manifest->image_length,
      .length = manifest->image_length - offsetof(manifest_t, image_length),
  };
  return kErrorOk;
}

// FIXME: Remove this after adding the entry_point field.
static_assert(sizeof(manifest_t) > 768 && sizeof(manifest_t) <= 1024,
              "kEntryPointOffset must be updated");

/**
 * Gets the entry point of an image.
 *
 * Entry point is the address that a boot stage jumps to handle execution to the
 * next stage in the boot chain. This function returns a `uintptr_t` instead of
 * a function pointer to accommodate for entry points with different parameters
 * and return types.
 *
 * @param manfiest A manifest.
 * @return The entry point.
 */
inline uintptr_t manifest_entry_point_address_get(const manifest_t *manifest) {
  // FIXME: Remove this after adding the entry_point field.
  enum { kEntryPointOffset = 1152 };
  return (uintptr_t)manifest + kEntryPointOffset;
}

// TODO: Move this definition to a more suitable place. Defined here for now
// until we implement the boot policy module or the flash driver.
/**
 * Flash slots.
 *
 * OpenTitan's flash is split into two slots: A and B. Each stage in the boot
 * chain is responsible for choosing and verifying the slot from which the next
 * stage in the boot chain is executed.
 */
typedef enum flash_slot {
  /**
   * Flash slot A.
   */
  kFlashSlotA,
  /**
   * Flash slot B.
   */
  kFlashSlotB,
} flash_slot_t;

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_
