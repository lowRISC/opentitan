// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Structs for reading and writing manifests of flash boot stage images.
//!
//! Note: The structs below must match the definitions in
//! sw/device/silicon_creator/lib/manifest.h.

#![deny(warnings)]
#![deny(unused)]
#![deny(unsafe_code)]

use std::mem::size_of;

use memoffset::offset_of;
use zerocopy::AsBytes;
use zerocopy::FromBytes;

// Currently, these definitions must be updated manually but they can be
// generated using the following commands (requires bindgen):
//   cargo install bindgen
//   cd "${REPO_TOP}"
//   bindgen --allowlist-type manifest_t --allowlist-var "MANIFEST_.*" \
//      --no-doc-comments --no-layout-tests \
//      sw/device/silicon_creator/lib/manifest.h \
//      -- -I./ -Isw/device/lib/base/freestanding

pub const MANIFEST_SIZE: u32 = 880;

/// Manifest for boot stage images stored in flash.
#[repr(C)]
#[derive(FromBytes, AsBytes, Debug, Default)]
pub struct Manifest {
    pub identifier: u32,
    pub reserved0: u32,
    pub signature: SigverifyRsaBuffer,
    pub image_length: u32,
    pub image_version: u32,
    pub image_timestamp: u64,
    pub exponent: u32,
    pub reserved1: u32,
    pub usage_constraints: [u32; 8usize],
    pub lockdown_info: [u32; 4usize],
    pub modulus: SigverifyRsaBuffer,
    pub extension0_offset: u32,
    pub extension0_checksum: u32,
    pub extension1_offset: u32,
    pub extension1_checksum: u32,
    pub extension2_offset: u32,
    pub extension2_checksum: u32,
    pub extension3_offset: u32,
    pub extension3_checksum: u32,
}

/// A type that holds 96 32-bit words for RSA-3072.
#[repr(C)]
#[derive(FromBytes, AsBytes, Debug)]
pub struct SigverifyRsaBuffer {
    pub data: [u32; 96usize],
}

impl Default for SigverifyRsaBuffer {
    fn default() -> Self {
        Self { data: [0; 96usize] }
    }
}

/// Checks the layout of the manifest struct.
///
/// Implemented as a function because using `offset_of!` at compile-time
/// requires a nightly compiler.
/// TODO(#6915): Convert this to a unit test after we start running rust tests during our builds.
pub fn check_manifest_layout() {
    assert_eq!(offset_of!(Manifest, identifier), 0);
    assert_eq!(offset_of!(Manifest, reserved0), 4);
    assert_eq!(offset_of!(Manifest, signature), 8);
    assert_eq!(offset_of!(Manifest, image_length), 392);
    assert_eq!(offset_of!(Manifest, image_version), 396);
    assert_eq!(offset_of!(Manifest, image_timestamp), 400);
    assert_eq!(offset_of!(Manifest, exponent), 408);
    assert_eq!(offset_of!(Manifest, reserved1), 412);
    assert_eq!(offset_of!(Manifest, usage_constraints), 416);
    assert_eq!(offset_of!(Manifest, lockdown_info), 448);
    assert_eq!(offset_of!(Manifest, modulus), 464);
    assert_eq!(offset_of!(Manifest, extension0_offset), 848);
    assert_eq!(offset_of!(Manifest, extension0_checksum), 852);
    assert_eq!(offset_of!(Manifest, extension1_offset), 856);
    assert_eq!(offset_of!(Manifest, extension1_checksum), 860);
    assert_eq!(offset_of!(Manifest, extension2_offset), 864);
    assert_eq!(offset_of!(Manifest, extension2_checksum), 868);
    assert_eq!(offset_of!(Manifest, extension3_offset), 872);
    assert_eq!(size_of::<Manifest>(), MANIFEST_SIZE as usize);
}
