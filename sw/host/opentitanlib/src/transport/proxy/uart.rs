// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use std::io::{ErrorKind, Read};
use std::rc::Rc;
use std::time::Duration;

use super::ProxyError;
use crate::io::nonblocking_help::NonblockingHelp;
use crate::io::uart::{FlowControl, Parity, Uart};
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

    fn do_read(&self, buf: &mut [u8], timeout: Option<Duration>) -> Result<usize> {
        let mut first_try = true;
        loop {
            {
                let mut uarts = self.inner.uarts.borrow_mut();
                let uart_record = uarts.get_mut(&self.instance).unwrap();
                match uart_record.pipe_receiver.read(buf) {
                    Ok(0) => (),
                    Ok(n) => return Ok(n),
                    Err(ref e) if e.kind() == ErrorKind::WouldBlock => (),
                    Err(e) => anyhow::bail!(e),
                }
            }
            if !first_try && timeout.is_some() {
                return Ok(0); // Timeout
            }
            self.inner.poll_for_async_data(timeout)?;
            first_try = false;
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

    fn set_break(&self, enable: bool) -> Result<()> {
        match self.execute_command(UartRequest::SetBreak(enable))? {
            UartResponse::SetBreak => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_parity(&self) -> Result<Parity> {
        match self.execute_command(UartRequest::GetParity)? {
            UartResponse::GetParity { parity } => Ok(parity),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_parity(&self, parity: Parity) -> Result<()> {
        match self.execute_command(UartRequest::SetParity(parity))? {
            UartResponse::SetParity => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_flow_control(&self) -> Result<FlowControl> {
        match self.execute_command(UartRequest::GetFlowControl)? {
            UartResponse::GetFlowControl { flow_control } => Ok(flow_control),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn set_flow_control(&self, flow_control: bool) -> Result<()> {
        match self.execute_command(UartRequest::SetFlowControl(flow_control))? {
            UartResponse::SetFlowControl => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn get_device_path(&self) -> Result<String> {
        match self.execute_command(UartRequest::GetDevicePath)? {
            UartResponse::GetDevicePath { path } => Ok(path),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// This function _may_ block.
    fn read(&self, buf: &mut [u8]) -> Result<usize> {
        self.do_read(buf, None)
    }

    /// Reads UART receive data into `buf`, returning the number of bytes read.
    /// The `timeout` may be used to specify a duration to wait for data.
    /// If timeout expires without any data arriving `Ok(0)` will be returned, never `Err(_)`.
    fn read_timeout(&self, buf: &mut [u8], timeout: Duration) -> Result<usize> {
        self.do_read(buf, Some(timeout))
    }

    /// Writes data from `buf` to the UART.
    fn write(&self, buf: &[u8]) -> Result<()> {
        match self.execute_command(UartRequest::Write { data: buf.to_vec() })? {
            UartResponse::Write => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn supports_nonblocking_read(&self) -> Result<bool> {
        Ok(true)
    }
    fn register_nonblocking_read(&self, registry: &mio::Registry, token: mio::Token) -> Result<()> {
        let mut uarts = self.inner.uarts.borrow_mut();
        let uart_record = uarts.get_mut(&self.instance).unwrap();
        uart_record.pipe_receiver.set_nonblocking(true)?;
        registry.register(
            &mut uart_record.pipe_receiver,
            token,
            mio::Interest::READABLE,
        )?;
        Ok(())
    }

    fn nonblocking_help(&self) -> Result<Rc<dyn NonblockingHelp>> {
        Ok(Rc::new(super::ProxyNonblockingHelp {
            inner: self.inner.clone(),
        }))
    }
}
