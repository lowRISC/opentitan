// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;

use super::ProxyError;
use crate::bail;
use crate::io::gpio::{GpioPin, PinMode, PullMode};
use crate::proxy::protocol::{GpioRequest, GpioResponse, Request, Response};
use crate::transport::proxy::{Inner, Proxy, Result};

pub struct ProxyGpioPin {
    inner: Rc<Inner>,
    pinname: String,
}

impl ProxyGpioPin {
    pub fn open(proxy: &Proxy, pinname: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&proxy.inner),
            pinname: pinname.to_string(),
        };
        Ok(result)
    }

    // Convenience method for issuing GPIO commands via proxy protocol.
    fn execute_command(&self, command: GpioRequest) -> Result<GpioResponse> {
        match self.inner.execute_command(Request::Gpio {
            id: self.pinname.clone(),
            command,
        })? {
            Response::Gpio(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl GpioPin for ProxyGpioPin {
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self) -> Result<bool> {
        match self.execute_command(GpioRequest::Read)? {
            GpioResponse::Read { value } => Ok(value),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, value: bool) -> Result<()> {
        match self.execute_command(GpioRequest::Write { logic: value })? {
            GpioResponse::Write => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        match self.execute_command(GpioRequest::SetMode { mode })? {
            GpioResponse::SetMode => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_pull_mode(&self, pull: PullMode) -> Result<()> {
        match self.execute_command(GpioRequest::SetPullMode { pull })? {
            GpioResponse::SetPullMode => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
