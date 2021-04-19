// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ---------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! ----------
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE
// FOLLOWING COMMAND:
// util/rom-ext-manifest-generator.py
//     --input-dir=sw/device/silicon_creator/rom_exts
//     --output-dir=<destination dir>
//     --output-files=rust

pub struct ManifestField {
    pub offset: usize,
    pub size_bytes: usize,
}

pub const ROM_EXT_MANIFEST_IDENTIFIER: ManifestField = ManifestField {
    offset: 0,
    size_bytes: 4,
};

pub const ROM_EXT_IMAGE_SIGNATURE: ManifestField = ManifestField {
    offset: 8,
    size_bytes: 384,
};

pub const ROM_EXT_IMAGE_LENGTH: ManifestField = ManifestField {
    offset: 392,
    size_bytes: 4,
};

pub const ROM_EXT_IMAGE_VERSION: ManifestField = ManifestField {
    offset: 396,
    size_bytes: 4,
};

pub const ROM_EXT_IMAGE_TIMESTAMP: ManifestField = ManifestField {
    offset: 400,
    size_bytes: 8,
};

pub const ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT: ManifestField =
    ManifestField {
        offset: 408,
        size_bytes: 4,
    };

pub const ROM_EXT_USAGE_CONSTRAINTS: ManifestField = ManifestField {
    offset: 416,
    size_bytes: 32,
};

pub const ROM_EXT_PERIPHERAL_LOCKDOWN_INFO: ManifestField = ManifestField {
    offset: 448,
    size_bytes: 16,
};

pub const ROM_EXT_SIGNATURE_KEY_MODULUS: ManifestField = ManifestField {
    offset: 464,
    size_bytes: 384,
};

pub const ROM_EXT_EXTENSION0_OFFSET: ManifestField = ManifestField {
    offset: 848,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION0_CHECKSUM: ManifestField = ManifestField {
    offset: 852,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION1_OFFSET: ManifestField = ManifestField {
    offset: 856,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION1_CHECKSUM: ManifestField = ManifestField {
    offset: 860,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION2_OFFSET: ManifestField = ManifestField {
    offset: 864,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION2_CHECKSUM: ManifestField = ManifestField {
    offset: 868,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION3_OFFSET: ManifestField = ManifestField {
    offset: 872,
    size_bytes: 4,
};

pub const ROM_EXT_EXTENSION3_CHECKSUM: ManifestField = ManifestField {
    offset: 876,
    size_bytes: 4,
};

/// Manifest offset signed_area_start from the base.
pub const ROM_EXT_SIGNED_AREA_START_OFFSET: usize = 392;

/// Manifest offset interrupt_vector from the base.
pub const ROM_EXT_INTERRUPT_VECTOR_OFFSET: usize = 1024;

/// Manifest offset entry_point from the base.
pub const ROM_EXT_ENTRY_POINT_OFFSET: usize = 1152;
