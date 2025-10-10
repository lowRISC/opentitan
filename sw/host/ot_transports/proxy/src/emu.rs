// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use std::collections::HashMap;

use opentitanlib::io::emu::{EmuState, EmuValue, Emulator};
use ot_proxy_proto::{EmuRequest, EmuResponse, Request, Response};

use super::{Inner, Proxy, ProxyError};

impl Inner {
    // Convenience method for issuing EMU commands via proxy protocol.
    fn execute_emu_command(&self, command: EmuRequest) -> Result<EmuResponse> {
        match self.execute_command(Request::Emu { command })? {
            Response::Emu(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl Emulator for Proxy {
    fn get_state(&self) -> Result<EmuState> {
        match self.inner.execute_emu_command(EmuRequest::GetState)? {
            EmuResponse::GetState { state } => Ok(state),
            _ => Err(ProxyError::UnexpectedReply().into()),
        }
    }

    fn start(&self, factory_reset: bool, args: &HashMap<String, EmuValue>) -> Result<()> {
        match self.inner.execute_emu_command(EmuRequest::Start {
            factory_reset,
            args: args.clone(),
        })? {
            EmuResponse::Start => Ok(()),
            _ => Err(ProxyError::UnexpectedReply().into()),
        }
    }

    fn stop(&self) -> Result<()> {
        match self.inner.execute_emu_command(EmuRequest::Stop)? {
            EmuResponse::Stop => Ok(()),
            _ => Err(ProxyError::UnexpectedReply().into()),
        }
    }
}
