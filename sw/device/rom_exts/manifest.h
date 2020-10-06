// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_ROM_EXTS_MANIFEST_H_
#define OPENTITAN_SW_DEVICE_ROM_EXTS_MANIFEST_H_

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Manifest field manifest_identifier offset from the base.
 */
#define ROM_EXT_MANIFEST_IDENTIFIER_OFFSET 0u

/**
 * Manifest field manifest_identifier size in bytes and words.
 */
#define ROM_EXT_MANIFEST_IDENTIFIER_SIZE_BYTES 4u
#define ROM_EXT_MANIFEST_IDENTIFIER_SIZE_WORDS 1u

/**
 * Manifest field image_signature offset from the base.
 */
#define ROM_EXT_IMAGE_SIGNATURE_OFFSET 8u

/**
 * Manifest field image_signature size in bytes and words.
 */
#define ROM_EXT_IMAGE_SIGNATURE_SIZE_BYTES 384u
#define ROM_EXT_IMAGE_SIGNATURE_SIZE_WORDS 96u

/**
 * Manifest field image_length offset from the base.
 */
#define ROM_EXT_IMAGE_LENGTH_OFFSET 392u

/**
 * Manifest field image_length size in bytes and words.
 */
#define ROM_EXT_IMAGE_LENGTH_SIZE_BYTES 4u
#define ROM_EXT_IMAGE_LENGTH_SIZE_WORDS 1u

/**
 * Manifest field image_version offset from the base.
 */
#define ROM_EXT_IMAGE_VERSION_OFFSET 396u

/**
 * Manifest field image_version size in bytes and words.
 */
#define ROM_EXT_IMAGE_VERSION_SIZE_BYTES 4u
#define ROM_EXT_IMAGE_VERSION_SIZE_WORDS 1u

/**
 * Manifest field image_timestamp offset from the base.
 */
#define ROM_EXT_IMAGE_TIMESTAMP_OFFSET 400u

/**
 * Manifest field image_timestamp size in bytes and words.
 */
#define ROM_EXT_IMAGE_TIMESTAMP_SIZE_BYTES 8u
#define ROM_EXT_IMAGE_TIMESTAMP_SIZE_WORDS 2u

/**
 * Manifest field signature_algorithm_identifier offset from the base.
 */
#define ROM_EXT_SIGNATURE_ALGORITHM_IDENTIFIER_OFFSET 408u

/**
 * Manifest field signature_algorithm_identifier size in bytes and words.
 */
#define ROM_EXT_SIGNATURE_ALGORITHM_IDENTIFIER_SIZE_BYTES 4u
#define ROM_EXT_SIGNATURE_ALGORITHM_IDENTIFIER_SIZE_WORDS 1u

/**
 * Manifest field exponent offset from the base.
 */
#define ROM_EXT_EXPONENT_OFFSET 412u

/**
 * Manifest field exponent size in bytes and words.
 */
#define ROM_EXT_EXPONENT_SIZE_BYTES 4u
#define ROM_EXT_EXPONENT_SIZE_WORDS 1u

/**
 * Manifest field usage_constraints offset from the base.
 */
#define ROM_EXT_USAGE_CONSTRAINTS_OFFSET 416u

/**
 * Manifest field usage_constraints size in bytes and words.
 */
#define ROM_EXT_USAGE_CONSTRAINTS_SIZE_BYTES 4u
#define ROM_EXT_USAGE_CONSTRAINTS_SIZE_WORDS 1u

/**
 * Manifest field peripheral_lockdown_info offset from the base.
 */
#define ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET 424u

/**
 * Manifest field peripheral_lockdown_info size in bytes and words.
 */
#define ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_BYTES 16u
#define ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_WORDS 4u

/**
 * Manifest field signature_public_key offset from the base.
 */
#define ROM_EXT_SIGNATURE_PUBLIC_KEY_OFFSET 440u

/**
 * Manifest field signature_public_key size in bytes and words.
 */
#define ROM_EXT_SIGNATURE_PUBLIC_KEY_SIZE_BYTES 384u
#define ROM_EXT_SIGNATURE_PUBLIC_KEY_SIZE_WORDS 96u

/**
 * Manifest field extension0_offset offset from the base.
 */
#define ROM_EXT_EXTENSION0_OFFSET_OFFSET 824u

/**
 * Manifest field extension0_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION0_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION0_OFFSET_SIZE_WORDS 1u

/**
 * Manifest field extension0_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION0_CHECKSUM_OFFSET 828u

/**
 * Manifest field extension0_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION0_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION0_CHECKSUM_SIZE_WORDS 1u

/**
 * Manifest field extension1_offset offset from the base.
 */
#define ROM_EXT_EXTENSION1_OFFSET_OFFSET 832u

/**
 * Manifest field extension1_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION1_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION1_OFFSET_SIZE_WORDS 1u

/**
 * Manifest field extension1_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION1_CHECKSUM_OFFSET 836u

/**
 * Manifest field extension1_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION1_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION1_CHECKSUM_SIZE_WORDS 1u

/**
 * Manifest field extension2_offset offset from the base.
 */
#define ROM_EXT_EXTENSION2_OFFSET_OFFSET 840u

/**
 * Manifest field extension2_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION2_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION2_OFFSET_SIZE_WORDS 1u

/**
 * Manifest field extension2_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION2_CHECKSUM_OFFSET 844u

/**
 * Manifest field extension2_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION2_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION2_CHECKSUM_SIZE_WORDS 1u

/**
 * Manifest field extension3_offset offset from the base.
 */
#define ROM_EXT_EXTENSION3_OFFSET_OFFSET 848u

/**
 * Manifest field extension3_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION3_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION3_OFFSET_SIZE_WORDS 1u

/**
 * Manifest field extension3_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION3_CHECKSUM_OFFSET 852u

/**
 * Manifest field extension3_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION3_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION3_CHECKSUM_SIZE_WORDS 1u

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_ROM_EXTS_MANIFEST_H_
