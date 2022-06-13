// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::collections::HashMap;
use std::rc::Rc;

use super::ProxyError;
use crate::io::emu::{EmuState, EmuValue, Emulator};
use crate::proxy::protocol::{EmuRequest, EmuResponse, Request, Response};
use crate::transport::proxy::{Inner, Proxy};

pub struct ProxyEmu {
    inner: Rc<Inner>,
}

impl ProxyEmu {
    pub fn open(proxy: &Proxy) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(&proxy.inner),
        })
    }

    // Convenience method for issuing EMU commands via proxy protocol.
    fn execute_command(&self, command: EmuRequest) -> Result<EmuResponse> {
        match self.inner.execute_command(Request::Emu { command })? {
            Response::Emu(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl Emulator for ProxyEmu {
    fn get_state(&self) -> Result<EmuState> {
        match self.execute_command(EmuRequest::GetState)? {
            EmuResponse::GetState { state } => Ok(state),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn start(&self, factory_reset: bool, args: &HashMap<String, EmuValue>) -> Result<()> {
        match self.execute_command(EmuRequest::Start {
            factory_reset,
            args: args.clone(),
        })? {
            EmuResponse::Start => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn stop(&self) -> Result<()> {
        match self.execute_command(EmuRequest::Stop)? {
            EmuResponse::Stop => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
