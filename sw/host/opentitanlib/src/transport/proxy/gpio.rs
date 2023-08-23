// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::rc::Rc;

use super::ProxyError;
use crate::io::gpio::{
    ClockNature, GpioMonitoring, GpioPin, MonitoringReadResponse, MonitoringStartResponse, PinMode,
    PullMode,
};
use crate::proxy::protocol::{
    GpioMonRequest, GpioMonResponse, GpioRequest, GpioResponse, Request, Response,
};
use crate::transport::proxy::{Inner, Proxy};

pub struct ProxyGpioPin {
    inner: Rc<Inner>,
    pinname: String,
    default_level: bool,
}

impl ProxyGpioPin {
    pub fn open(proxy: &Proxy, pinname: &str, default_level: bool) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&proxy.inner),
            pinname: pinname.to_string(),
            default_level,
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
    /// Reads the value of the GPIO pin `id`.
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

    fn reset(&self) -> Result<()> {
        self.write(self.default_level)
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

    fn get_internal_pin_name(&self) -> Option<&str> {
        Some(&self.pinname)
    }
}

pub struct GpioMonitoringImpl {
    inner: Rc<Inner>,
}

impl GpioMonitoringImpl {
    pub fn new(proxy: &Proxy) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(&proxy.inner),
        })
    }

    // Convenience method for issuing GPIO monitoring commands via proxy protocol.
    fn execute_command(&self, command: GpioMonRequest) -> Result<GpioMonResponse> {
        match self
            .inner
            .execute_command(Request::GpioMonitoring { command })?
        {
            Response::GpioMonitoring(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl GpioMonitoring for GpioMonitoringImpl {
    fn get_clock_nature(&self) -> Result<ClockNature> {
        match self.execute_command(GpioMonRequest::GetClockNature)? {
            GpioMonResponse::GetClockNature { resp } => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn monitoring_start(&self, pins: &[&dyn GpioPin]) -> Result<MonitoringStartResponse> {
        let pins = pins
            .iter()
            .map(|p| p.get_internal_pin_name().unwrap().to_string())
            .collect::<Vec<String>>();
        match self.execute_command(GpioMonRequest::Start { pins })? {
            GpioMonResponse::Start { resp } => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn monitoring_read(
        &self,
        pins: &[&dyn GpioPin],
        continue_monitoring: bool,
    ) -> Result<MonitoringReadResponse> {
        let pins = pins
            .iter()
            .map(|p| p.get_internal_pin_name().unwrap().to_string())
            .collect::<Vec<String>>();
        match self.execute_command(GpioMonRequest::Read {
            pins,
            continue_monitoring,
        })? {
            GpioMonResponse::Read { resp } => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
