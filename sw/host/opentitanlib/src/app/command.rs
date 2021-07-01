// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::transport::Transport;
use anyhow::Result;
use erased_serde::Serialize;
pub use opentitantool_derive::*;

/// The `CommandDispatch` trait should be implemented for all leaf structures
/// in the application's command hierarchy.  It can be automatically derived
/// on internal nodes in the heirarchy.  See the documentation for
/// [`opentitantool_derive`].
pub trait CommandDispatch {
    fn run(&self, transport: &mut dyn Transport) -> Result<Option<Box<dyn Serialize>>>;
}
