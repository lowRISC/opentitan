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

% for name, region in regions:
/// Manifest field ${name} offset from the base.
pub const ${region.offset_name().as_c_define()}:u32 = ${region.base_addr};

/// Manifest field ${name} size in bytes.
pub const ${region.size_bytes_name().as_c_define()}:u32 = ${region.size_bytes};

/// Manifest field ${name} size in words.
pub const ${region.size_words_name().as_c_define()}:u32 = ${region.size_words};

% endfor

% for name, offset in offsets:
/// Manifest offset ${name} from the base.
pub const ${offset.offset_name().as_c_define()}:u32 = ${offset.offset};

%endfor
