// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::app::TransportWrapper;
use anyhow::Result;
pub use opentitantool_derive::*;
use serde_annotate::Annotate;
use std::any::Any;

/// The `CommandDispatch` trait should be implemented for all leaf structures
/// in the application's command hierarchy.  It can be automatically derived
/// on internal nodes in the heirarchy.  See the documentation for
/// [`opentitantool_derive`].
///
/// The `context` parameter can be used to carry information from prior levels
/// in the command hierarchy to the next level.  This is typically used to
/// implement parameters on interior nodes before the next layer of subcommands.
pub trait CommandDispatch {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>>;

    /// For optimization.  Indicates whether this command expects to not run concurrently with
    /// other manipulations of the backend debugger.  Only long-running commands such as `console`
    /// will return `false` to indicate that to the contrary they expect other invocations of
    /// `opentitantool` to run during their lifespan.  Returning `true` here will allow
    /// opentitanlib the optimization of keeping USB handles open for the duration of the `run()`
    /// call, and even across `run()` of multiple commands if `--exec` is used.
    fn exclusive_use_of_transport(&self) -> bool {
        true
    }
}
