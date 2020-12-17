// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ----------
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE
// FOLLOWING COMMAND:
// util/rom-ext-manifest-generator.py
//     --input-dir=sw/device/rom_exts
//     --output-dir=<destination dir>
//     --output-files=rust

/// Manifest field manifest_identifier offset from the base.
pub const ROM_EXT_MANIFEST_IDENTIFIER_OFFSET: u32 = 0;

/// Manifest field manifest_identifier size in bytes.
pub const ROM_EXT_MANIFEST_IDENTIFIER_SIZE_BYTES: u32 = 4;

/// Manifest field manifest_identifier size in words.
pub const ROM_EXT_MANIFEST_IDENTIFIER_SIZE_WORDS: u32 = 1;

/// Manifest field image_signature offset from the base.
pub const ROM_EXT_IMAGE_SIGNATURE_OFFSET: u32 = 8;

/// Manifest field image_signature size in bytes.
pub const ROM_EXT_IMAGE_SIGNATURE_SIZE_BYTES: u32 = 384;

/// Manifest field image_signature size in words.
pub const ROM_EXT_IMAGE_SIGNATURE_SIZE_WORDS: u32 = 96;

/// Manifest field image_length offset from the base.
pub const ROM_EXT_IMAGE_LENGTH_OFFSET: u32 = 392;

/// Manifest field image_length size in bytes.
pub const ROM_EXT_IMAGE_LENGTH_SIZE_BYTES: u32 = 4;

/// Manifest field image_length size in words.
pub const ROM_EXT_IMAGE_LENGTH_SIZE_WORDS: u32 = 1;

/// Manifest field image_version offset from the base.
pub const ROM_EXT_IMAGE_VERSION_OFFSET: u32 = 396;

/// Manifest field image_version size in bytes.
pub const ROM_EXT_IMAGE_VERSION_SIZE_BYTES: u32 = 4;

/// Manifest field image_version size in words.
pub const ROM_EXT_IMAGE_VERSION_SIZE_WORDS: u32 = 1;

/// Manifest field image_timestamp offset from the base.
pub const ROM_EXT_IMAGE_TIMESTAMP_OFFSET: u32 = 400;

/// Manifest field image_timestamp size in bytes.
pub const ROM_EXT_IMAGE_TIMESTAMP_SIZE_BYTES: u32 = 8;

/// Manifest field image_timestamp size in words.
pub const ROM_EXT_IMAGE_TIMESTAMP_SIZE_WORDS: u32 = 2;

/// Manifest field signature_key_public_exponent offset from the base.
pub const ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT_OFFSET: u32 = 408;

/// Manifest field signature_key_public_exponent size in bytes.
pub const ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT_SIZE_BYTES: u32 = 4;

/// Manifest field signature_key_public_exponent size in words.
pub const ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT_SIZE_WORDS: u32 = 1;

/// Manifest field usage_constraints offset from the base.
pub const ROM_EXT_USAGE_CONSTRAINTS_OFFSET: u32 = 416;

/// Manifest field usage_constraints size in bytes.
pub const ROM_EXT_USAGE_CONSTRAINTS_SIZE_BYTES: u32 = 32;

/// Manifest field usage_constraints size in words.
pub const ROM_EXT_USAGE_CONSTRAINTS_SIZE_WORDS: u32 = 8;

/// Manifest field peripheral_lockdown_info offset from the base.
pub const ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET: u32 = 448;

/// Manifest field peripheral_lockdown_info size in bytes.
pub const ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_BYTES: u32 = 16;

/// Manifest field peripheral_lockdown_info size in words.
pub const ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_WORDS: u32 = 4;

/// Manifest field signature_key_modulus offset from the base.
pub const ROM_EXT_SIGNATURE_KEY_MODULUS_OFFSET: u32 = 464;

/// Manifest field signature_key_modulus size in bytes.
pub const ROM_EXT_SIGNATURE_KEY_MODULUS_SIZE_BYTES: u32 = 384;

/// Manifest field signature_key_modulus size in words.
pub const ROM_EXT_SIGNATURE_KEY_MODULUS_SIZE_WORDS: u32 = 96;

/// Manifest field extension0_offset offset from the base.
pub const ROM_EXT_EXTENSION0_OFFSET_OFFSET: u32 = 848;

/// Manifest field extension0_offset size in bytes.
pub const ROM_EXT_EXTENSION0_OFFSET_SIZE_BYTES: u32 = 4;

/// Manifest field extension0_offset size in words.
pub const ROM_EXT_EXTENSION0_OFFSET_SIZE_WORDS: u32 = 1;

/// Manifest field extension0_checksum offset from the base.
pub const ROM_EXT_EXTENSION0_CHECKSUM_OFFSET: u32 = 852;

/// Manifest field extension0_checksum size in bytes.
pub const ROM_EXT_EXTENSION0_CHECKSUM_SIZE_BYTES: u32 = 4;

/// Manifest field extension0_checksum size in words.
pub const ROM_EXT_EXTENSION0_CHECKSUM_SIZE_WORDS: u32 = 1;

/// Manifest field extension1_offset offset from the base.
pub const ROM_EXT_EXTENSION1_OFFSET_OFFSET: u32 = 856;

/// Manifest field extension1_offset size in bytes.
pub const ROM_EXT_EXTENSION1_OFFSET_SIZE_BYTES: u32 = 4;

/// Manifest field extension1_offset size in words.
pub const ROM_EXT_EXTENSION1_OFFSET_SIZE_WORDS: u32 = 1;

/// Manifest field extension1_checksum offset from the base.
pub const ROM_EXT_EXTENSION1_CHECKSUM_OFFSET: u32 = 860;

/// Manifest field extension1_checksum size in bytes.
pub const ROM_EXT_EXTENSION1_CHECKSUM_SIZE_BYTES: u32 = 4;

/// Manifest field extension1_checksum size in words.
pub const ROM_EXT_EXTENSION1_CHECKSUM_SIZE_WORDS: u32 = 1;

/// Manifest field extension2_offset offset from the base.
pub const ROM_EXT_EXTENSION2_OFFSET_OFFSET: u32 = 864;

/// Manifest field extension2_offset size in bytes.
pub const ROM_EXT_EXTENSION2_OFFSET_SIZE_BYTES: u32 = 4;

/// Manifest field extension2_offset size in words.
pub const ROM_EXT_EXTENSION2_OFFSET_SIZE_WORDS: u32 = 1;

/// Manifest field extension2_checksum offset from the base.
pub const ROM_EXT_EXTENSION2_CHECKSUM_OFFSET: u32 = 868;

/// Manifest field extension2_checksum size in bytes.
pub const ROM_EXT_EXTENSION2_CHECKSUM_SIZE_BYTES: u32 = 4;

/// Manifest field extension2_checksum size in words.
pub const ROM_EXT_EXTENSION2_CHECKSUM_SIZE_WORDS: u32 = 1;

/// Manifest field extension3_offset offset from the base.
pub const ROM_EXT_EXTENSION3_OFFSET_OFFSET: u32 = 872;

/// Manifest field extension3_offset size in bytes.
pub const ROM_EXT_EXTENSION3_OFFSET_SIZE_BYTES: u32 = 4;

/// Manifest field extension3_offset size in words.
pub const ROM_EXT_EXTENSION3_OFFSET_SIZE_WORDS: u32 = 1;

/// Manifest field extension3_checksum offset from the base.
pub const ROM_EXT_EXTENSION3_CHECKSUM_OFFSET: u32 = 876;

/// Manifest field extension3_checksum size in bytes.
pub const ROM_EXT_EXTENSION3_CHECKSUM_SIZE_BYTES: u32 = 4;

/// Manifest field extension3_checksum size in words.
pub const ROM_EXT_EXTENSION3_CHECKSUM_SIZE_WORDS: u32 = 1;

/// Manifest offset signed_area_start from the base.
pub const ROM_EXT_SIGNED_AREA_START_OFFSET: u32 = 392;

/// Manifest offset interrupt_vector from the base.
pub const ROM_EXT_INTERRUPT_VECTOR_OFFSET: u32 = 1024;

/// Manifest offset entry_point from the base.
pub const ROM_EXT_ENTRY_POINT_OFFSET: u32 = 1152;
