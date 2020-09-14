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
 * ROM_EXT manifest field manifest_identifier offset from the base.
 */
#define ROM_EXT_MANIFEST_IDENTIFIER_OFFSET 0u

/**
 * ROM_EXT manifest field manifest_identifier size in bytes and words.
 */
#define ROM_EXT_MANIFEST_IDENTIFIER_SIZE_BYTES 4u
#define ROM_EXT_MANIFEST_IDENTIFIER_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field image_signature offset from the base.
 */
#define ROM_EXT_IMAGE_SIGNATURE_OFFSET 8u

/**
 * ROM_EXT manifest field image_signature size in bytes and words.
 */
#define ROM_EXT_IMAGE_SIGNATURE_SIZE_BYTES 384u
#define ROM_EXT_IMAGE_SIGNATURE_SIZE_WORDS 96u

/**
 * ROM_EXT manifest field image_length offset from the base.
 */
#define ROM_EXT_IMAGE_LENGTH_OFFSET 392u

/**
 * ROM_EXT manifest field image_length size in bytes and words.
 */
#define ROM_EXT_IMAGE_LENGTH_SIZE_BYTES 4u
#define ROM_EXT_IMAGE_LENGTH_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field image_version offset from the base.
 */
#define ROM_EXT_IMAGE_VERSION_OFFSET 396u

/**
 * ROM_EXT manifest field image_version size in bytes and words.
 */
#define ROM_EXT_IMAGE_VERSION_SIZE_BYTES 4u
#define ROM_EXT_IMAGE_VERSION_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field image_timestamp offset from the base.
 */
#define ROM_EXT_IMAGE_TIMESTAMP_OFFSET 400u

/**
 * ROM_EXT manifest field image_timestamp size in bytes and words.
 */
#define ROM_EXT_IMAGE_TIMESTAMP_SIZE_BYTES 8u
#define ROM_EXT_IMAGE_TIMESTAMP_SIZE_WORDS 2u

/**
 * ROM_EXT manifest field signature_algorithm_identifier offset from the base.
 */
#define ROM_EXT_SIGNATURE_ALGORITHM_IDENTIFIER_OFFSET 408u

/**
 * ROM_EXT manifest field signature_algorithm_identifier size in bytes and
 * words.
 */
#define ROM_EXT_SIGNATURE_ALGORITHM_IDENTIFIER_SIZE_BYTES 4u
#define ROM_EXT_SIGNATURE_ALGORITHM_IDENTIFIER_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field exponent offset from the base.
 */
#define ROM_EXT_EXPONENT_OFFSET 412u

/**
 * ROM_EXT manifest field exponent size in bytes and words.
 */
#define ROM_EXT_EXPONENT_SIZE_BYTES 4u
#define ROM_EXT_EXPONENT_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field usage_constraints offset from the base.
 */
#define ROM_EXT_USAGE_CONSTRAINTS_OFFSET 416u

/**
 * ROM_EXT manifest field usage_constraints size in bytes and words.
 */
#define ROM_EXT_USAGE_CONSTRAINTS_SIZE_BYTES 4u
#define ROM_EXT_USAGE_CONSTRAINTS_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field peripheral_lockdown_info offset from the base.
 */
#define ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET 424u

/**
 * ROM_EXT manifest field peripheral_lockdown_info size in bytes and words.
 */
#define ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_BYTES 16u
#define ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_WORDS 4u

/**
 * ROM_EXT manifest field signature_public_key offset from the base.
 */
#define ROM_EXT_SIGNATURE_PUBLIC_KEY_OFFSET 440u

/**
 * ROM_EXT manifest field signature_public_key size in bytes and words.
 */
#define ROM_EXT_SIGNATURE_PUBLIC_KEY_SIZE_BYTES 384u
#define ROM_EXT_SIGNATURE_PUBLIC_KEY_SIZE_WORDS 96u

/**
 * ROM_EXT manifest field extension0_offset offset from the base.
 */
#define ROM_EXT_EXTENSION0_OFFSET_OFFSET 824u

/**
 * ROM_EXT manifest field extension0_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION0_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION0_OFFSET_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension0_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION0_CHECKSUM_OFFSET 828u

/**
 * ROM_EXT manifest field extension0_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION0_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION0_CHECKSUM_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension1_offset offset from the base.
 */
#define ROM_EXT_EXTENSION1_OFFSET_OFFSET 832u

/**
 * ROM_EXT manifest field extension1_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION1_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION1_OFFSET_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension1_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION1_CHECKSUM_OFFSET 836u

/**
 * ROM_EXT manifest field extension1_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION1_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION1_CHECKSUM_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension2_offset offset from the base.
 */
#define ROM_EXT_EXTENSION2_OFFSET_OFFSET 840u

/**
 * ROM_EXT manifest field extension2_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION2_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION2_OFFSET_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension2_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION2_CHECKSUM_OFFSET 844u

/**
 * ROM_EXT manifest field extension2_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION2_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION2_CHECKSUM_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension3_offset offset from the base.
 */
#define ROM_EXT_EXTENSION3_OFFSET_OFFSET 848u

/**
 * ROM_EXT manifest field extension3_offset size in bytes and words.
 */
#define ROM_EXT_EXTENSION3_OFFSET_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION3_OFFSET_SIZE_WORDS 1u

/**
 * ROM_EXT manifest field extension3_checksum offset from the base.
 */
#define ROM_EXT_EXTENSION3_CHECKSUM_OFFSET 852u

/**
 * ROM_EXT manifest field extension3_checksum size in bytes and words.
 */
#define ROM_EXT_EXTENSION3_CHECKSUM_SIZE_BYTES 4u
#define ROM_EXT_EXTENSION3_CHECKSUM_SIZE_WORDS 1u

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_ROM_EXTS_MANIFEST_H_
