// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicBool, Ordering};

mod application_key;
mod flash;
mod flash_info;
mod misc;
pub mod owner;
mod rescue;

pub use application_key::{ApplicationKeyDomain, OwnerApplicationKey};
pub use flash::{FlashFlags, OwnerFlashConfig, OwnerFlashRegion};
pub use flash_info::{OwnerFlashInfoConfig, OwnerInfoPage};
pub use misc::{KeyMaterial, OwnershipKeyAlg, TlvHeader, TlvTag};
pub use owner::{OwnerBlock, OwnerConfigItem, SramExecMode};
pub use rescue::{CommandTag, OwnerRescueConfig, RescueType};

pub struct GlobalFlags;

static DEBUG: AtomicBool = AtomicBool::new(false);

impl GlobalFlags {
    /// Set the value of the ownership debug flag.  This controls the serialization
    /// of header and reserved fields in the ownership structs.
    pub fn set_debug(v: bool) {
        DEBUG.store(v, Ordering::Relaxed);
    }

    // Used by the serde serializer to query whether or not a field should be serialized.
    pub fn not_debug<T>(_: &T) -> bool {
        !DEBUG.load(Ordering::Relaxed)
    }
}
