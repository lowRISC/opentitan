// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_

#include <stddef.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_key.h"
#include "sw/device/silicon_creator/lib/sigverify/spx_key.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Usage constraints.
 *
 * This struct is used to constrain a boot stage image to a set of devices based
 * on their device IDs, creator and/or owner manufacturing states, and life
 * cycle states. Bits of `selector_bits` determine which fields (or individual
 * words of a field as in the case of `device_id`) must be read from the
 * hardware during verification. Unselected fields must be set to
 * `MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL` to be able to generate a
 * consistent value during verification.
 */
typedef struct manifest_usage_constraints {
  /**
   * Usage constraint selector bits.
   *
   * The bits of this field are mapped to the remaining fields as follows:
   * - Bits 0-7: `device_id[0-7]`
   * - Bit 8   : `manuf_state_creator`
   * - Bit 9   : `manuf_state_owner`
   * - Bit 10  : `life_cycle_state`
   */
  uint32_t selector_bits;
  /**
   * Device identifier value which is compared against the `DEVICE_ID` value
   * stored in the `HW_CFG` partition in OTP.
   *
   * Mapped to bits 0-7 of `selector_bits`.
   */
  lifecycle_device_id_t device_id;
  /**
   * Device Silicon Creator manufacting status compared against the
   * `CREATOR_SW_MANUF_STATUS` value stored in the `CREATOR_SW_CFG` partition in
   * OTP.
   *
   * Mapped to bit 8 of `selector_bits`.
   */
  uint32_t manuf_state_creator;
  /**
   * Device Silicon Owner manufacturing status compared against the
   * `OWNER_SW_MANUF_STATUS` value stored in the `OWNER_SW_CFG` partition in
   * OTP.
   *
   * Mapped to bit 9 of `selector_bits`.
   */
  uint32_t manuf_state_owner;
  /**
   * Device life cycle status compared against the status reported by the life
   * cycle controller.
   *
   * Mapped to bit 10 of `selector_bits`.
   */
  uint32_t life_cycle_state;
} manifest_usage_constraints_t;

/**
 * Value to use for unselected usage constraint words.
 */
#define MANIFEST_USAGE_CONSTRAINT_UNSELECTED_WORD_VAL 0xA5A5A5A5

/**
 * `selector_bits` bit indices for usage constraints fields.
 */
enum {
  /**
   * Bits mapped to the `device_id` field.
   */
  kManifestSelectorBitDeviceIdFirst = 0,
  kManifestSelectorBitDeviceIdLast = 7,

  /**
   * Bit mapped to the `manuf_state_creator` field.
   */
  kManifestSelectorBitManufStateCreator = 8,
  /**
   * Bit mapped to the `manuf_state_owner` field.
   */
  kManifestSelectorBitManufStateOwner = 9,
  /**
   * Bit mapped to the `life_cycle_state` field.
   */
  kManifestSelectorBitLifeCycleState = 10,
};

/**
 * Manifest for boot stage images stored in flash.
 *
 * OpenTitan secure boot, at a minimum, consists of three boot stages: ROM,
 * ROM_EXT, and the first owner boot stage, e.g. BL0. ROM is stored in the
 * read-only ROM while remaining stages are stored in flash. This structure
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
   * SPHINCS+ signature of the image.
   *
   * TODO(#17824): Make this optional.
   */
  sigverify_spx_signature_t spx_signature;
  /**
   * RSA signature of the image.
   *
   * RSASSA-PKCS1-v1_5 signature of the image generated using a 3072-bit RSA
   * private key and the SHA-256 hash function. The signed region of an image
   * starts immediately after this field and ends at the end of the image.
   *
   * On-target verification should also integrate usage constraints comparison
   * to signature verification to harden it against potential attacks. During
   * verification, the digest of an image should be computed by first reading
   * the usage constraints from the hardware and then concatenating the rest of
   * the image:
   *
   *   digest = SHA256(usage_constraints_from_hw || rest_of_the_image)
   *
   * The start and the length of the region that should be concatenated to the
   * usage constraints read from the hardware can be obtained using
   * `manifest_digest_region_get()`.
   */
  sigverify_rsa_buffer_t rsa_signature;
  /**
   * Usage constraints.
   */
  manifest_usage_constraints_t usage_constraints;
  /**
   * SPHINCS+ public key of the signer.
   */
  sigverify_spx_key_t spx_key;
  /**
   * Modulus of the signer's 3072-bit RSA public key.
   */
  sigverify_rsa_buffer_t rsa_modulus;
  /**
   * Address translation (hardened boolean).
   */
  uint32_t address_translation;
  /**
   * Manifest identifier.
   */
  uint32_t identifier;
  /**
   * Offset of the end of the signed region relative to the start of the
   * manifest.
   */
  uint32_t signed_region_end;
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
  uint32_t timestamp[2];
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

OT_ASSERT_MEMBER_OFFSET(manifest_t, spx_signature, 0);
OT_ASSERT_MEMBER_OFFSET(manifest_t, rsa_signature, 7856);
OT_ASSERT_MEMBER_OFFSET(manifest_t, usage_constraints, 8240);
OT_ASSERT_MEMBER_OFFSET(manifest_t, spx_key, 8288);
OT_ASSERT_MEMBER_OFFSET(manifest_t, rsa_modulus, 8320);
OT_ASSERT_MEMBER_OFFSET(manifest_t, address_translation, 8704);
OT_ASSERT_MEMBER_OFFSET(manifest_t, identifier, 8708);
OT_ASSERT_MEMBER_OFFSET(manifest_t, signed_region_end, 8712);
OT_ASSERT_MEMBER_OFFSET(manifest_t, length, 8716);
OT_ASSERT_MEMBER_OFFSET(manifest_t, version_major, 8720);
OT_ASSERT_MEMBER_OFFSET(manifest_t, version_minor, 8724);
OT_ASSERT_MEMBER_OFFSET(manifest_t, security_version, 8728);
OT_ASSERT_MEMBER_OFFSET(manifest_t, timestamp, 8732);
OT_ASSERT_MEMBER_OFFSET(manifest_t, binding_value, 8740);
OT_ASSERT_MEMBER_OFFSET(manifest_t, max_key_version, 8772);
OT_ASSERT_MEMBER_OFFSET(manifest_t, code_start, 8776);
OT_ASSERT_MEMBER_OFFSET(manifest_t, code_end, 8780);
OT_ASSERT_MEMBER_OFFSET(manifest_t, entry_point, 8784);
OT_ASSERT_SIZE(manifest_t, CHIP_MANIFEST_SIZE);

/**
 * Region of an image that should be included in the digest computation.
 */
typedef struct manifest_digest_region {
  /**
   * Start of the region.
   */
  const void *start;
  /**
   * Length of the region in bytes.
   */
  size_t length;
} manifest_digest_region_t;

#if defined(OT_PLATFORM_RV32) || defined(MANIFEST_UNIT_TEST_)
/**
 * Checks the fields of a manifest.
 *
 * This function performs several basic checks to ensure that
 * - Executable region is non-empty, inside the image, located after the
 * manifest, and word aligned, and
 * - Entry point is inside the executable region and word aligned.
 *
 * @param manfiest A manifest.
 * @return Result of the operation.
 */
inline rom_error_t manifest_check(const manifest_t *manifest) {
  // Signed region must be inside the image.
  if (manifest->signed_region_end > manifest->length) {
    return kErrorManifestBadSignedRegion;
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
 * Gets the region of the image that should be included in the digest
 * computation.
 *
 * Digest region of an image starts immediately after the `usage_constraints`
 * field of its manifest and ends at the end of the image.
 *
 * @param manifest A manifest.
 * return digest_region Region of the image that should be included in the
 * digest computation.
 */
inline manifest_digest_region_t manifest_digest_region_get(
    const manifest_t *manifest) {
  enum {
    kDigestRegionOffset = offsetof(manifest_t, usage_constraints) +
                          sizeof(manifest->usage_constraints),
  };
  return (manifest_digest_region_t){
      .start = (const char *)manifest + kDigestRegionOffset,
      .length = manifest->signed_region_end - kDigestRegionOffset,
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
#else   // defined(OT_PLATFORM_RV32) || defined(MANIFEST_UNIT_TEST_)
/**
 * Declarations for the functions above that should be defined in tests.
 */
rom_error_t manifest_check(const manifest_t *manifest);
manifest_digest_region_t manifest_digest_region_get(const manifest_t *manifest);
epmp_region_t manifest_code_region_get(const manifest_t *manifest);
uintptr_t manifest_entry_point_get(const manifest_t *manifest);
#endif  // defined(OT_PLATFORM_RV32) || defined(MANIFEST_UNIT_TEST_)

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_MANIFEST_H_
