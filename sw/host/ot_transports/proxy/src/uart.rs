// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::pin::Pin;
use std::rc::Rc;
use std::task::Poll;
use std::time::Duration;

use anyhow::{Result, bail};
use tokio::io::AsyncRead;

use opentitanlib::io::console::ConsoleDevice;
use opentitanlib::io::uart::{FlowControl, Parity, Uart};
use opentitanlib::util::runtime::MultiWaker;
use ot_proxy_proto::{Request, Response, UartRequest, UartResponse};

use super::{Inner, Proxy, ProxyError};

pub struct ProxyUart {
    inner: Rc<Inner>,
    instance: String,
    multi_waker: MultiWaker,
}

impl ProxyUart {
    pub fn open(proxy: &Proxy, instance: &str) -> Result<Self> {
        let result = Self {
            inner: proxy.inner.clone(),
            instance: instance.to_string(),
            multi_waker: MultiWaker::new(),
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

impl ConsoleDevice for ProxyUart {
    fn poll_read(&self, cx: &mut std::task::Context<'_>, buf: &mut [u8]) -> Poll<Result<usize>> {
        self.inner.poll_for_async_data()?;

        let mut uarts = self.inner.uarts.borrow_mut();
        let uart_record = uarts.get_mut(&self.instance).unwrap();
        let mut read_buf = tokio::io::ReadBuf::new(buf);
        match self.multi_waker.poll_with(cx, |cx| {
            Pin::new(&mut uart_record.pipe_receiver).poll_read(cx, &mut read_buf)
        })? {
            Poll::Ready(()) => Poll::Ready(Ok(read_buf.filled().len())),
            Poll::Pending => {
                // `self.inner` currently does not yet support context notification.
                opentitanlib::util::runtime::poll_later(cx, Duration::from_millis(1))
            }
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

    fn set_break(&self, enable: bool) -> Result<()> {
        match self.execute_command(UartRequest::SetBreak(enable))? {
            UartResponse::SetBreak => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}
