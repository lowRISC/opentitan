// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/runtime/epmp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/manifest_size.h"
#include "sw/device/silicon_creator/lib/sigverify_rsa_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Manifest for boot stage images stored in flash.
 *
 * OpenTitan secure boot, at a minimum, consists of four boot stages: ROM,
 * ROM_EXT, BL0, and Kernel. ROM is stored in the read-only Mask ROM while
 * remaining stages are stored in flash. This structure must be placed at the
 * start of ROM_EXT and BL0 images so that ROM and ROM_EXT can verify the
 * integrity and authenticity of the next stage and configure peripherals as
 * needed before handing over execution.
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
  keymgr_binding_value_t binding_value;
  /**
   * Maximum allowed version for keys generated at the next boot stage.
   */
  uint32_t max_key_version;
  /**
   * Modulus of the signer's RSA public key.
   */
  sigverify_rsa_buffer_t modulus;
  /**
   * Offset of the start of the executable region of the image from the start
   * of the manifest in bytes.
   */
  uint32_t code_start;
  /**
   * Offset of the end of the executable region (exclusive) of the image from
   * the start of the manifest in bytes.
   */
  uint32_t code_end;
  /**
   * Offset of the first instruction to execute in the image from the start of
   * the manifest in bytes.
   */
  uint32_t entry_point;
  /**
   * Trailing padding (due to image_timestamp and the size of the struct).
   */
  uint32_t padding;
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
OT_ASSERT_MEMBER_OFFSET(manifest_t, code_start, 832);
OT_ASSERT_MEMBER_OFFSET(manifest_t, code_end, 836);
OT_ASSERT_MEMBER_OFFSET(manifest_t, entry_point, 840);
OT_ASSERT_MEMBER_OFFSET(manifest_t, padding, 844);
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

/**
 * Gets the executable region of the image.
 *
 * This function also checks that the executable region is non-empty, inside
 * the image, located after the manifest, and word aligned.
 *
 * @param manifest A manifest.
 * @param[out] code_region Executable region of the image.
 * @return The result of the operation.
 */
inline rom_error_t manifest_code_region_get(const manifest_t *manifest,
                                            epmp_region_t *code_region) {
  if (manifest->code_start >= manifest->code_end ||
      manifest->code_start < sizeof(manifest_t) ||
      manifest->code_end > manifest->image_length ||
      // FIXME: Replace this when we have a function/macro for alignment checks.
      (manifest->code_start & 0x3) != 0 || (manifest->code_end & 0x3) != 0) {
    return kErrorManifestBadCodeRegion;
  }
  *code_region = (epmp_region_t){
      .start = (uintptr_t)manifest + manifest->code_start,
      .end = (uintptr_t)manifest + manifest->code_end,
  };
  return kErrorOk;
}

/**
 * Gets the entry point of an image.
 *
 * Entry point is the address that a boot stage jumps to transfer execution to
 * the next stage in the boot chain. This function returns a `uintptr_t` instead
 * of a function pointer to accommodate for entry points with different
 * parameters and return types.
 *
 * This function also checks that the entry point is inside both the image and
 * the executable region of the image and word aligned.
 *
 * @param manfiest A manifest.
 * @param[out] entry_point Entry point address.
 * @return The result of the operation.
 */
inline rom_error_t manifest_entry_point_get(const manifest_t *manifest,
                                            uintptr_t *entry_point) {
  if (manifest->entry_point < manifest->code_start ||
      manifest->entry_point >= manifest->code_end ||
      manifest->entry_point >= manifest->image_length ||
      // FIXME: Replace this when we have a function/macro for alignment checks.
      (manifest->entry_point & 0x3) != 0) {
    return kErrorManifestBadEntryPoint;
  }
  *entry_point = (uintptr_t)manifest + manifest->entry_point;
  return kErrorOk;
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
