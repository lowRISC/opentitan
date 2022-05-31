// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::rc::Rc;
use std::time::Duration;

use super::ProxyError;
use crate::io::uart::Uart;
use crate::proxy::protocol::{Request, Response, UartRequest, UartResponse};
use crate::transport::proxy::{Inner, Proxy};

pub struct ProxyUart {
    inner: Rc<Inner>,
    instance: String,
}

impl ProxyUart {
    pub fn open(proxy: &Proxy, instance: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(&proxy.inner),
            instance: instance.to_string(),
        };
        Ok(result)
    }

    // Convenience method for issuing UART commands via proxy protocol.
    fn execute_command(&self, command: UartRequest) -> Result<UartResponse> {
        match self.inner.execute_command(Request::Uart {
            id: self.instance.clone(),
            command,
        })? {
            Response::Uart(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl Uart for ProxyUart {
    /// Returns the UART baudrate.  May return zero for virtual UARTs.
    fn get_baudrate(&self) -> Result<u32> {
        match self.execute_command(UartRequest::GetBaudrate)? {
            UartResponse::GetBaudrate { rate } => Ok(rate),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Sets the UART baudrate.  May do nothing for virtual UARTs.
    fn set_baudrate(&self, rate: u32) -> Result<()> {
        match self.execute_command(UartRequest::SetBaudrate { rate })? {
            UartResponse::SetBaudrate => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        match self.execute_command(UartRequest::Read {
            timeout_millis: None,
            len: buf.len() as u32,
        })? {
            UartResponse::Read { data } => {
                buf[..data.len()].clone_from_slice(&data);
                Ok(data.len())
            }
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        match self.execute_command(UartRequest::Read {
            timeout_millis: Some(timeout.as_millis() as u32),
            len: buf.len() as u32,
        })? {
            UartResponse::Read { data } => {
                buf[..data.len()].clone_from_slice(&data);
                Ok(data.len())
            }
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        match self.execute_command(UartRequest::Write { data: buf.to_vec() })? {
            UartResponse::Write => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
