// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

/// In order to provide nonblocking functionality (e.g. in the `Uart` trait), some transport
/// backends may need help from the main `mio` event loop.  This trait allows the transport to
/// register its internal event sources with a poll registery used by the main loop, and the main
/// loop will then be reponsible for calling `nonblocking_help` every time one of the transports
/// internal sources become ready.
pub trait NonblockingHelp {
    fn register_nonblocking_help(
        &self,
        _registry: &mio::Registry,
        _token: mio::Token,
    ) -> Result<()>;
    fn nonblocking_help(&self) -> Result<()>;
}

/// Implementation to be used by backends which do not need to put any internal source into
/// `mio::poll()` of the main event loop.
pub struct NoNonblockingHelp;
impl NonblockingHelp for NoNonblockingHelp {
    fn register_nonblocking_help(
        &self,
        _registry: &mio::Registry,
        _token: mio::Token,
    ) -> Result<()> {
        Ok(())
    }
    fn nonblocking_help(&self) -> Result<()> {
        Ok(())
    }
}
