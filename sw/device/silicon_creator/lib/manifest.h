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
   * Image major version.
   */
  uint32_t image_major_version;
  /**
   * Image minor version.
   */
  uint32_t image_minor_version;
  /**
   * Image timestamp.
   */
  uint64_t image_timestamp;
  /**
   * Exponent of the signer's RSA public key.
   */
  uint32_t exponent;
  /**
   * Binding value used by key manager to derive secret values.
   *
   * A change in this value changes the secret value of key manager, and
   * consequently, the versioned keys and identity seeds generated at subsequent
   * boot stages.
   */
  uint32_t binding_value[8];
  /**
   * Maximum allowed version for keys generated at the next boot stage.
   */
  uint32_t max_key_version;
  /**
   * Modulus of the signer's RSA public key.
   */
  sigverify_rsa_buffer_t modulus;
} manifest_t;

OT_ASSERT_MEMBER_OFFSET(manifest_t, identifier, 0);
OT_ASSERT_MEMBER_OFFSET(manifest_t, signature, 4);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_length, 388);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_major_version, 392);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_minor_version, 396);
OT_ASSERT_MEMBER_OFFSET(manifest_t, image_timestamp, 400);
OT_ASSERT_MEMBER_OFFSET(manifest_t, exponent, 408);
OT_ASSERT_MEMBER_OFFSET(manifest_t, binding_value, 412);
OT_ASSERT_MEMBER_OFFSET(manifest_t, max_key_version, 444);
OT_ASSERT_MEMBER_OFFSET(manifest_t, modulus, 448);
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
