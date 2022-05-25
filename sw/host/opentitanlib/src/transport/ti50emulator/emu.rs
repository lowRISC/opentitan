// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::collections::HashMap;

use crate::io::emu::{EmuState, EmuValue, Emulator};
use crate::transport::ti50emulator::Ti50Emulator;
use crate::transport::TransportError;
use anyhow::Result;

/// Structure representing `Emulator` sub-process based on TockOS host-emulation architecture.
pub struct Ti50SubProcess {}

impl Ti50SubProcess {
    /// Create a new `Ti50SubProcess` instance.
    pub fn open(_ti50: &Ti50Emulator) -> Result<Self> {
        Err(TransportError::UnsupportedOperation.into())
    }
}

impl Emulator for Ti50SubProcess {
    /// Simple function with return `EmuState` representing current state of Emulator instance.
    fn get_state(&self) -> Result<EmuState> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Start emulator sub-process with provided arguments.
    fn start(&self, _factory_reset: bool, _args: &HashMap<String, EmuValue>) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Stop emulator sub-process.
    fn stop(&self) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }
}
