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

% for name, region in regions:
pub const ${region.name.as_c_define()}: ManifestField = ManifestField {
    offset: ${region.base_addr},
    size_bytes: ${region.size_bytes},
};

% endfor

% for name, offset in offsets:
/// Manifest offset ${name} from the base.
pub const ${offset.offset_name().as_c_define()}:usize = ${offset.offset};

%endfor
