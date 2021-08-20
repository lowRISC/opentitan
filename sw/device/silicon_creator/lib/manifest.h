// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/epmp.h"
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
 * OpenTitan secure boot, at a minimum, consists of three boot stages: ROM,
 * ROM_EXT, and the first owner boot stage, e.g. BL0. ROM is stored in the
 * read-only Mask ROM while remaining stages are stored in flash. This structure
 * must be placed at the start of ROM_EXT and first owner boot stage images so
 * that ROM and ROM_EXT can verify the integrity and authenticity of the next
 * stage and configure peripherals as needed before handing over execution.
 *
 * Use of this struct for stages following the first owner boot stage is
 * optional.
 *
 * Note: The definitions in
 * sw/host/rom_ext_image_tools/signer/image/src/manifest.rs must be updated if
 * this struct is modified. Please see the instructions in that file.
 */
typedef struct manifest {
  /**
   * Image signature.
   *
   * RSASSA-PKCS1-v1_5 signature of the image generated using a 3072-bit RSA
   * private key and the SHA-256 hash function. The signed region of an image
   * starts immediately after this field and ends at the end of the image. The
   * start and the length of the signed region can be obtained using
   * `manifest_signed_region_get`.
   */
  sigverify_rsa_buffer_t signature;
  /**
   * Modulus of the signer's 3072-bit RSA public key.
   */
  sigverify_rsa_buffer_t modulus;
  /**
   * Exponent of the signer's RSA public key.
   */
  uint32_t exponent;
  /**
   * Manifest identifier.
   */
  uint32_t identifier;
  /**
   * Length of the image including the manifest in bytes.
   *
   * Note that the length includes the signature but the signature is excluded
   * from the signed region.
   */
  uint32_t length;
  /**
   * Image major version.
   */
  uint32_t version_major;
  /**
   * Image minor version.
   */
  uint32_t version_minor;
  /**
   * Security version of the image used for anti-rollback protection.
   */
  uint32_t security_version;
  /**
   * Image timestamp.
   *
   * Unix timestamp that gives the creation time of the image, seconds since
   * 00:00:00 on January 1, 1970 UTC (the Unix Epoch).
   */
  uint64_t timestamp;
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
} manifest_t;

OT_ASSERT_MEMBER_OFFSET(manifest_t, signature, 0);
OT_ASSERT_MEMBER_OFFSET(manifest_t, modulus, 384);
OT_ASSERT_MEMBER_OFFSET(manifest_t, exponent, 768);
OT_ASSERT_MEMBER_OFFSET(manifest_t, identifier, 772);
OT_ASSERT_MEMBER_OFFSET(manifest_t, length, 776);
OT_ASSERT_MEMBER_OFFSET(manifest_t, version_major, 780);
OT_ASSERT_MEMBER_OFFSET(manifest_t, version_minor, 784);
OT_ASSERT_MEMBER_OFFSET(manifest_t, security_version, 788);
OT_ASSERT_MEMBER_OFFSET(manifest_t, timestamp, 792);
OT_ASSERT_MEMBER_OFFSET(manifest_t, binding_value, 800);
OT_ASSERT_MEMBER_OFFSET(manifest_t, max_key_version, 832);
OT_ASSERT_MEMBER_OFFSET(manifest_t, code_start, 836);
OT_ASSERT_MEMBER_OFFSET(manifest_t, code_end, 840);
OT_ASSERT_MEMBER_OFFSET(manifest_t, entry_point, 844);
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
 * Allowed bounds for the `length` field.
 */
// FIXME: Update min value after we have a fairly representative ROM_EXT.
#define MANIFEST_LENGTH_FIELD_MIN MANIFEST_SIZE
#define MANIFEST_LENGTH_FIELD_MAX 65536

/**
 * Checks the fields of a manifest.
 *
 * This function performs several basic checks to ensure that
 * - Length of the image is within a reasonable range,
 * - Executable region is non-empty, inside the image, located after the
 * manifest, and word aligned, and
 * - Entry point is inside the executable region and word aligned.
 *
 * @param manfiest A manifest.
 * @return Result of the operation.
 */
inline rom_error_t manifest_check(const manifest_t *manifest) {
  // Length of the image must be within bounds.
  if (manifest->length < MANIFEST_LENGTH_FIELD_MIN ||
      manifest->length > MANIFEST_LENGTH_FIELD_MAX) {
    return kErrorManifestBadLength;
  }

  // Executable region must be empty, inside the image, located after the
  // manifest, and word aligned.
  if (manifest->code_start >= manifest->code_end ||
      manifest->code_start < sizeof(manifest_t) ||
      manifest->code_end > manifest->length ||
      (manifest->code_start & 0x3) != 0 || (manifest->code_end & 0x3) != 0) {
    return kErrorManifestBadCodeRegion;
  }

  // Entry point must be inside the executable region and word aligned.
  if (manifest->entry_point < manifest->code_start ||
      manifest->entry_point >= manifest->code_end ||
      (manifest->entry_point & 0x3) != 0) {
    return kErrorManifestBadEntryPoint;
  }

  return kErrorOk;
}

/**
 * Gets the signed region of an image.
 *
 * @param manifest A manifest
 * return signed_region Signed region of an image.
 */
inline manifest_signed_region_t manifest_signed_region_get(
    const manifest_t *manifest) {
  return (manifest_signed_region_t){
      .start = (const char *)manifest + sizeof(manifest->signature),
      .length = manifest->length - sizeof(manifest->signature),
  };
}

/**
 * Gets the executable region of the image.
 *
 * @param manifest A manifest.
 * return Executable region of the image.
 */
inline epmp_region_t manifest_code_region_get(const manifest_t *manifest) {
  return (epmp_region_t){
      .start = (uintptr_t)manifest + manifest->code_start,
      .end = (uintptr_t)manifest + manifest->code_end,
  };
}

/**
 * Gets the entry point of an image.
 *
 * Entry point is the address that a boot stage jumps to transfer execution to
 * the next stage in the boot chain. This function returns a `uintptr_t` instead
 * of a function pointer to accommodate for entry points with different
 * parameters and return types.
 *
 * @param manfiest A manifest.
 * return Entry point address.
 */
inline uintptr_t manifest_entry_point_get(const manifest_t *manifest) {
  return (uintptr_t)manifest + manifest->entry_point;
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
