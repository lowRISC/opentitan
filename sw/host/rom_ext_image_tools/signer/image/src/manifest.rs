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

pub const MANIFEST_SIZE: u32 = 848;

/// Manifest for boot stage images stored in flash.
#[repr(C)]
#[derive(FromBytes, AsBytes, Debug, Default)]
pub struct Manifest {
    pub signature: SigverifyRsaBuffer,
    pub modulus: SigverifyRsaBuffer,
    pub exponent: u32,
    pub identifier: u32,
    pub length: u32,
    pub version_major: u32,
    pub version_minor: u32,
    pub security_version: u32,
    pub timestamp: u64,
    pub binding_value: KeymgrBindingValue,
    pub max_key_version: u32,
    pub code_start: u32,
    pub code_end: u32,
    pub entry_point: u32,
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
    assert_eq!(offset_of!(Manifest, signature), 0);
    assert_eq!(offset_of!(Manifest, modulus), 384);
    assert_eq!(offset_of!(Manifest, exponent), 768);
    assert_eq!(offset_of!(Manifest, identifier), 772);
    assert_eq!(offset_of!(Manifest, length), 776);
    assert_eq!(offset_of!(Manifest, version_major), 780);
    assert_eq!(offset_of!(Manifest, version_minor), 784);
    assert_eq!(offset_of!(Manifest, security_version), 788);
    assert_eq!(offset_of!(Manifest, timestamp), 792);
    assert_eq!(offset_of!(Manifest, binding_value), 800);
    assert_eq!(offset_of!(Manifest, max_key_version), 832);
    assert_eq!(offset_of!(Manifest, code_start), 836);
    assert_eq!(offset_of!(Manifest, code_end), 840);
    assert_eq!(offset_of!(Manifest, entry_point), 844);
    assert_eq!(size_of::<Manifest>(), MANIFEST_SIZE as usize);
}
