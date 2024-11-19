// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Result};
use std::cell::Cell;
use std::rc::Rc;
use std::time::Duration;

use super::ProxyError;
use crate::io::gpio;
use crate::io::i2c::{Bus, DeviceStatus, I2cError, Mode, Transfer};
use crate::proxy::protocol::{
    I2cRequest, I2cResponse, I2cTransferRequest, I2cTransferResponse, Request, Response,
};
use crate::transport::proxy::{Inner, Proxy};

pub struct ProxyI2c {
    inner: Rc<Inner>,
    instance: String,
    default_address: Cell<Option<u8>>,
}

impl ProxyI2c {
    pub fn open(proxy: &Proxy, instance: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&proxy.inner),
            instance: instance.to_string(),
            default_address: Cell::new(None),
        };
        Ok(result)
    }

    // Convenience method for issuing I2C commands via proxy protocol.
    fn execute_command(&self, command: I2cRequest) -> Result<I2cResponse> {
        match self.inner.execute_command(Request::I2c {
            id: self.instance.clone(),
            command,
        })? {
            Response::I2c(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

fn i2c_pin_name(pin: Option<&Rc<dyn gpio::GpioPin>>) -> Result<Option<String>> {
    if let Some(pin) = pin {
        let Some(name) = pin.get_internal_pin_name() else {
            bail!(I2cError::InvalidPin)
        };
        Ok(Some(name.to_string()))
    } else {
        Ok(None)
    }
}

impl Bus for ProxyI2c {
    fn set_mode(&self, mode: Mode) -> Result<()> {
        match mode {
            Mode::Host => match self.execute_command(I2cRequest::SetModeHost)? {
                I2cResponse::SetModeHost => Ok(()),
                _ => bail!(ProxyError::UnexpectedReply()),
            },
            Mode::Device(addr) => {
                match self.execute_command(I2cRequest::SetModeDevice { addr })? {
                    I2cResponse::SetModeDevice => Ok(()),
                    _ => bail!(ProxyError::UnexpectedReply()),
                }
            }
        }
    }

    fn get_max_speed(&self) -> Result<u32> {
        match self.execute_command(I2cRequest::GetMaxSpeed)? {
            I2cResponse::GetMaxSpeed { speed } => Ok(speed),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
    fn set_max_speed(&self, value: u32) -> Result<()> {
        match self.execute_command(I2cRequest::SetMaxSpeed { value })? {
            I2cResponse::SetMaxSpeed => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_pins(
        &self,
        serial_clock: Option<&Rc<dyn gpio::GpioPin>>,
        serial_data: Option<&Rc<dyn gpio::GpioPin>>,
        gsc_ready: Option<&Rc<dyn gpio::GpioPin>>,
    ) -> Result<()> {
        match self.execute_command(I2cRequest::SetPins {
            serial_clock: i2c_pin_name(serial_clock)?,
            serial_data: i2c_pin_name(serial_data)?,
            gsc_ready: i2c_pin_name(gsc_ready)?,
        })? {
            I2cResponse::SetPins => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_default_address(&self, addr: u8) -> Result<()> {
        self.default_address.set(Some(addr));
        Ok(())
    }

    fn run_transaction(&self, address: Option<u8>, transaction: &mut [Transfer]) -> Result<()> {
        let mut req: Vec<I2cTransferRequest> = Vec::new();
        for transfer in &*transaction {
            // &* to treat as non-mutable in this loop
            match transfer {
                Transfer::Read(rbuf) => req.push(I2cTransferRequest::Read {
                    len: rbuf.len() as u32,
                }),
                Transfer::Write(wbuf) => req.push(I2cTransferRequest::Write {
                    data: wbuf.to_vec(),
                }),
                Transfer::GscReady => req.push(I2cTransferRequest::GscReady),
            }
        }
        match self.execute_command(I2cRequest::RunTransaction {
            address: address.or(self.default_address.get()),
            transaction: req,
        })? {
            I2cResponse::RunTransaction { transaction: resp } => {
                ensure!(
                    resp.len() == transaction.len(),
                    ProxyError::UnexpectedReply()
                );
                for pair in resp.iter().zip(transaction.iter_mut()) {
                    match pair {
                        (I2cTransferResponse::Read { data }, Transfer::Read(rbuf)) => {
                            rbuf.clone_from_slice(data);
                        }
                        (I2cTransferResponse::Write, Transfer::Write(_)) => (),
                        (I2cTransferResponse::GscReady, Transfer::GscReady) => (),
                        _ => bail!(ProxyError::UnexpectedReply()),
                    }
                }
                Ok(())
            }
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_device_status(&self, timeout: Duration) -> Result<DeviceStatus> {
        match self.execute_command(I2cRequest::GetDeviceStatus {
            timeout_millis: timeout.as_millis() as u32,
        })? {
            I2cResponse::GetDeviceStatus { status } => Ok(status),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn prepare_read_data(&self, data: &[u8], sticky: bool) -> Result<()> {
        match self.execute_command(I2cRequest::PrepareReadData {
            data: data.to_vec(),
            sticky,
        })? {
            I2cResponse::PrepareReadData => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
