// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use crate::uart::console::ExitStatus;

pub trait ConsolePlugin {
    /// Process a chunk of bytes.
    ///
    /// The plugin may consume or transform the bytes, and return the processed
    /// bytes for the next plugin in the chain.
    ///
    /// Returns `Ok(processed_bytes)` if processing is successful and
    /// there are bytes to pass to the next plugin.
    /// Returns `Err` if an unrecoverable error occurs during processing.
    fn process_bytes(&mut self, bytes: Vec<u8>) -> Result<Vec<u8>>;

    /// Returns `ExitStatus` if the console session should terminate.
    ///
    /// The plugin might return None, which means it doesn't want to terminate
    /// the console session at this moment.
    fn exit_status(&self) -> Option<ExitStatus>;
}
