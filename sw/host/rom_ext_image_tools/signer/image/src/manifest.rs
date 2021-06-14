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

pub const MANIFEST_SIZE: u32 = 832;

/// Manifest for boot stage images stored in flash.
#[repr(C)]
#[derive(FromBytes, AsBytes, Debug, Default)]
pub struct Manifest {
    pub identifier: u32,
    pub signature: SigverifyRsaBuffer,
    pub image_length: u32,
    pub image_major_version: u32,
    pub image_minor_version: u32,
    pub image_timestamp: u64,
    pub exponent: u32,
    pub binding_value: KeymgrBindingValue,
    pub max_key_version: u32,
    pub modulus: SigverifyRsaBuffer,
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

#[repr(C)]
#[derive(FromBytes, AsBytes, Debug, Default)]
pub struct KeymgrBindingValue {
        pub data: [u32; 8usize],
}

/// Checks the layout of the manifest struct.
///
/// Implemented as a function because using `offset_of!` at compile-time
/// requires a nightly compiler.
/// TODO(#6915): Convert this to a unit test after we start running rust tests during our builds.
pub fn check_manifest_layout() {
    assert_eq!(offset_of!(Manifest, identifier), 0);
    assert_eq!(offset_of!(Manifest, signature), 4);
    assert_eq!(offset_of!(Manifest, image_length), 388);
    assert_eq!(offset_of!(Manifest, image_major_version), 392);
    assert_eq!(offset_of!(Manifest, image_minor_version), 396);
    assert_eq!(offset_of!(Manifest, image_timestamp), 400);
    assert_eq!(offset_of!(Manifest, exponent), 408);
    assert_eq!(offset_of!(Manifest, binding_value), 412);
    assert_eq!(offset_of!(Manifest, max_key_version), 444);
    assert_eq!(offset_of!(Manifest, modulus), 448);
    assert_eq!(size_of::<Manifest>(), MANIFEST_SIZE as usize);
}
