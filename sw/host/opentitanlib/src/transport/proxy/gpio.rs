// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::rc::Rc;
use std::time::Duration;

use super::ProxyError;
use crate::io::gpio::{
    BitbangEntry, ClockNature, DacBangEntry, GpioBitbangOperation, GpioBitbanging,
    GpioDacBangOperation, GpioError, GpioMonitoring, GpioPin, MonitoringReadResponse,
    MonitoringStartResponse, PinMode, PullMode,
};
use crate::proxy::protocol::{
    BitbangEntryRequest, BitbangEntryResponse, DacBangEntryRequest, GpioBitRequest,
    GpioBitResponse, GpioDacRequest, GpioDacResponse, GpioMonRequest, GpioMonResponse, GpioRequest,
    GpioResponse, Request, Response,
};
use crate::transport::proxy::{Inner, Proxy};

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

    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        analog_value: Option<f32>,
    ) -> Result<()> {
        match self.execute_command(GpioRequest::MultiSet {
            mode,
            value,
            pull,
            analog_value,
        })? {
            GpioResponse::MultiSet => Ok(()),
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

pub struct GpioBitbangingImpl {
    inner: Rc<Inner>,
}

impl GpioBitbangingImpl {
    pub fn new(proxy: &Proxy) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(&proxy.inner),
        })
    }

    // Convenience method for issuing GPIO bitbanging commands via proxy protocol.
    fn execute_command(&self, command: GpioBitRequest) -> Result<GpioBitResponse> {
        match self
            .inner
            .execute_command(Request::GpioBitbanging { command })?
        {
            Response::GpioBitbanging(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    // Convenience method for issuing GPIO dac-banging commands via proxy protocol.
    fn execute_dac_command(&self, command: GpioDacRequest) -> Result<GpioDacResponse> {
        match self
            .inner
            .execute_command(Request::GpioDacBanging { command })?
        {
            Response::GpioDacBanging(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl GpioBitbanging for GpioBitbangingImpl {
    fn start<'a>(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: Box<[BitbangEntry<'a, 'a>]>,
    ) -> Result<Box<dyn GpioBitbangOperation<'a, 'a> + 'a>> {
        let pins = pins
            .iter()
            .map(|p| p.get_internal_pin_name().unwrap().to_string())
            .collect::<Vec<String>>();

        let mut req: Vec<BitbangEntryRequest> = Vec::new();
        for entry in waveform.iter() {
            match entry {
                BitbangEntry::Write(wbuf) => req.push(BitbangEntryRequest::Write {
                    data: wbuf.to_vec(),
                }),
                BitbangEntry::Both(wbuf, rbuf) => {
                    ensure!(
                        rbuf.len() == wbuf.len(),
                        GpioError::MismatchedDataLength(wbuf.len(), rbuf.len())
                    );
                    req.push(BitbangEntryRequest::Both {
                        data: wbuf.to_vec(),
                    })
                }
                BitbangEntry::WriteOwned(buf) => {
                    req.push(BitbangEntryRequest::Write { data: buf.to_vec() })
                }
                BitbangEntry::BothOwned(buf) => {
                    req.push(BitbangEntryRequest::Both { data: buf.to_vec() })
                }
                BitbangEntry::Delay(ticks) => req.push(BitbangEntryRequest::Delay {
                    clock_ticks: *ticks,
                }),
                BitbangEntry::Await { mask, pattern } => req.push(BitbangEntryRequest::Await {
                    mask: *mask,
                    pattern: *pattern,
                }),
            }
        }
        match self.execute_command(GpioBitRequest::Start {
            pins,
            clock_ns: clock_tick.as_nanos() as u64,
            entries: req,
        })? {
            GpioBitResponse::Start => Ok(Box::new(GpioBitbangOperationImpl {
                inner: Rc::clone(&self.inner),
                waveform,
            })),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn dac_start(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: Box<[DacBangEntry]>,
    ) -> Result<Box<dyn GpioDacBangOperation>> {
        let pins = pins
            .iter()
            .map(|p| p.get_internal_pin_name().unwrap().to_string())
            .collect::<Vec<String>>();

        let mut req: Vec<DacBangEntryRequest> = Vec::new();
        for entry in waveform.iter() {
            match entry {
                DacBangEntry::Write(wbuf) => req.push(DacBangEntryRequest::Write {
                    data: wbuf.to_vec(),
                }),
                DacBangEntry::WriteOwned(wbuf) => req.push(DacBangEntryRequest::Write {
                    data: wbuf.to_vec(),
                }),
                DacBangEntry::Delay(ticks) => req.push(DacBangEntryRequest::Delay {
                    clock_ticks: *ticks,
                }),
                DacBangEntry::Linear(ticks) => req.push(DacBangEntryRequest::Linear {
                    clock_ticks: *ticks,
                }),
            }
        }
        match self.execute_dac_command(GpioDacRequest::Start {
            pins,
            clock_ns: clock_tick.as_nanos() as u64,
            entries: req,
        })? {
            GpioDacResponse::Start => Ok(Box::new(GpioDacBangOperationImpl {
                inner: Rc::clone(&self.inner),
            })),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

pub struct GpioBitbangOperationImpl<'a> {
    inner: Rc<Inner>,
    waveform: Box<[BitbangEntry<'a, 'a>]>,
}

impl<'a> GpioBitbangOperationImpl<'a> {
    // Convenience method for issuing GPIO bitbanging commands via proxy protocol.
    fn execute_command(&self, command: GpioBitRequest) -> Result<GpioBitResponse> {
        match self
            .inner
            .execute_command(Request::GpioBitbanging { command })?
        {
            Response::GpioBitbanging(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl<'a> GpioBitbangOperation<'a, 'a> for GpioBitbangOperationImpl<'a> {
    fn query(&mut self) -> Result<bool> {
        match self.execute_command(GpioBitRequest::Query)? {
            GpioBitResponse::QueryNotDone => Ok(false),
            GpioBitResponse::QueryDone { entries: resp } => {
                ensure!(
                    resp.len() == self.waveform.len(),
                    ProxyError::UnexpectedReply()
                );
                for pair in resp.iter().zip(self.waveform.iter_mut()) {
                    match pair {
                        (BitbangEntryResponse::Both { data }, BitbangEntry::Both(_, rbuf)) => {
                            rbuf.clone_from_slice(data);
                        }
                        (BitbangEntryResponse::Write, BitbangEntry::Write(_)) => (),
                        (BitbangEntryResponse::Delay, BitbangEntry::Delay(_)) => (),
                        (BitbangEntryResponse::Await, BitbangEntry::Await { .. }) => (),
                        _ => bail!(ProxyError::UnexpectedReply()),
                    }
                }
                Ok(true)
            }
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_result(self: Box<Self>) -> Result<Box<[BitbangEntry<'a, 'a>]>> {
        Ok(self.waveform)
    }
}

pub struct GpioDacBangOperationImpl {
    inner: Rc<Inner>,
}

impl GpioDacBangOperationImpl {
    // Convenience method for issuing GPIO dacbanging commands via proxy protocol.
    fn execute_command(&self, command: GpioDacRequest) -> Result<GpioDacResponse> {
        match self
            .inner
            .execute_command(Request::GpioDacBanging { command })?
        {
            Response::GpioDacBanging(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl GpioDacBangOperation for GpioDacBangOperationImpl {
    fn query(&mut self) -> Result<bool> {
        match self.execute_command(GpioDacRequest::Query)? {
            GpioDacResponse::QueryNotDone => Ok(false),
            GpioDacResponse::QueryDone => Ok(true),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
