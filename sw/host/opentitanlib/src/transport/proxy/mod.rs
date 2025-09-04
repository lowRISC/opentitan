// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::io::ErrorKind;
use std::rc::Rc;

use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::task::AbortHandle;

use crate::bootstrap::BootstrapOptions;
use crate::impl_serializable_error;
use crate::io::emu::Emulator;
use crate::io::gpio::{GpioBitbanging, GpioMonitoring, GpioPin};
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::proxy::protocol::{
    AsyncMessage, Message, ProxyRequest, ProxyResponse, Request, Response, UartRequest,
    UartResponse,
};
use crate::transport::{Capabilities, Capability, ProxyOps, Transport, TransportError};

mod emu;
mod gpio;
mod i2c;
mod spi;
mod uart;

#[derive(Debug, Error, Serialize, Deserialize)]
pub enum ProxyError {
    #[error("Unexpected reply")]
    UnexpectedReply(),
    #[error("JSON encoding: {0}")]
    JsonEncoding(String),
    #[error("JSON decoding: {0}")]
    JsonDecoding(String),
}
impl_serializable_error!(ProxyError);

/// Implementation of the Transport trait backed by connection to a remote OpenTitan tool
/// session process.
pub struct Proxy {
    inner: Rc<Inner>,
}

impl Proxy {
    /// Establish connection with a running session process.
    pub fn open(host: Option<&str>, port: u16) -> Result<Self> {
        let _enter_guard = crate::util::runtime().enter();

        let host = host.unwrap_or("localhost");
        let conn = crate::util::runtime::block_on(TcpStream::connect(&(host, port)))
            .map_err(|e| TransportError::ProxyConnectError(host.to_string(), e.to_string()))?;
        // Disable Nagle's algorithm to ensure reasonable communication latency.
        conn.set_nodelay(true)?;

        // Launch a new task for receiver messages.
        // We do not just poll messages when we have a pending request, as there are asynchronous
        // messages that we want to handle ASAP.
        let (conn_rx, conn_tx) = conn.into_split();
        let (resp_send, resp_recv) = tokio::sync::mpsc::channel(32);
        let recv_task = tokio::task::spawn(async move {
            if let Err(err) = Self::recv_messages(conn_rx, resp_send).await {
                log::warn!("Receving failed with {err}");
            }
        });

        Ok(Self {
            inner: Rc::new(Inner {
                conn_tx: RefCell::new(conn_tx),
                resp_recv: RefCell::new(resp_recv),
                uarts: RefCell::new(HashMap::new()),
                uart_channel_map: RefCell::new(HashMap::new()),
                recv_task: recv_task.abort_handle(),
            }),
        })
    }

    async fn recv_messages(
        conn_rx: OwnedReadHalf,
        resp_send: tokio::sync::mpsc::Sender<Message>,
    ) -> Result<()> {
        let mut conn_rx = tokio::io::BufReader::new(conn_rx);
        let mut buf = Vec::new();

        loop {
            buf.clear();
            let len = conn_rx.read_until(b'\n', &mut buf).await?;
            if len == 0 {
                bail!(io::Error::new(
                    ErrorKind::UnexpectedEof,
                    "Server unexpectedly closed connection"
                ));
            }

            let msg = serde_json::from_slice::<Message>(&buf)?;
            resp_send.send(msg).await.context("sender closed")?;
        }
    }
}

struct UartRecord {
    pub uart: Rc<dyn Uart>,
    pub pipe_sender: tokio::io::WriteHalf<tokio::io::SimplexStream>,
    pub pipe_receiver: tokio::io::ReadHalf<tokio::io::SimplexStream>,
}

struct Inner {
    conn_tx: RefCell<OwnedWriteHalf>,
    resp_recv: RefCell<tokio::sync::mpsc::Receiver<Message>>,
    pub uarts: RefCell<HashMap<String, UartRecord>>,
    uart_channel_map: RefCell<HashMap<u32, String>>,
    recv_task: AbortHandle,
}

impl Drop for Inner {
    fn drop(&mut self) {
        self.recv_task.abort()
    }
}

impl Inner {
    /// Helper method for sending one JSON request and receiving the response.  Called as part
    /// of the implementation of every method of the sub-traits (gpio, uart, spi, i2c).
    fn execute_command(&self, req: Request) -> Result<Response> {
        self.send_json_request(req).context("json encoding")?;
        loop {
            match crate::util::runtime::block_on(self.resp_recv.borrow_mut().recv())
                .context("dequeueing")?
            {
                Message::Res(res) => match res {
                    Ok(value) => return Ok(value),
                    Err(e) => return Err(anyhow::Error::from(e)),
                },
                Message::Async { channel, msg } => self.process_async_data(channel, msg)?,
                _ => bail!(ProxyError::UnexpectedReply()),
            }
        }
    }

    fn poll_for_async_data(&self) -> Result<()> {
        while let Ok(msg) = self.resp_recv.borrow_mut().try_recv() {
            match msg {
                Message::Async { channel, msg } => self.process_async_data(channel, msg)?,
                _ => bail!(ProxyError::UnexpectedReply()),
            }
        }
        Ok(())
    }

    fn process_async_data(&self, channel: u32, msg: AsyncMessage) -> Result<()> {
        match msg {
            AsyncMessage::UartData { data } => {
                if let Some(uart_instance) = self.uart_channel_map.borrow().get(&channel) {
                    if let Some(uart_record) = self.uarts.borrow_mut().get_mut(uart_instance) {
                        crate::util::runtime::block_on(async {
                            uart_record.pipe_sender.write_all(&data).await
                        })?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Send a one-line JSON encoded requests, terminated with one newline.
    #[expect(clippy::await_holding_refcell_ref)] // false positive
    fn send_json_request(&self, req: Request) -> Result<()> {
        let mut vec = serde_json::to_vec(&Message::Req(req))?;
        vec.push(b'\n');

        crate::util::runtime::block_on(async {
            let mut conn = self.conn_tx.borrow_mut();
            conn.write_all(&vec).await?;
            conn.flush().await?;
            Ok(())
        })
    }
}

pub struct ProxyOpsImpl {
    inner: Rc<Inner>,
}

impl ProxyOpsImpl {
    pub fn new(proxy: &Proxy) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(&proxy.inner),
        })
    }

    // Convenience method for issuing Proxy-only commands via proxy protocol.
    fn execute_command(&self, command: ProxyRequest) -> Result<ProxyResponse> {
        match self.inner.execute_command(Request::Proxy(command))? {
            Response::Proxy(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl ProxyOps for ProxyOpsImpl {
    fn provides_map(&self) -> Result<HashMap<String, String>> {
        match self.execute_command(ProxyRequest::Provides {})? {
            ProxyResponse::Provides { provides_map } => Ok(provides_map),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn bootstrap(&self, options: &BootstrapOptions, payload: &[u8]) -> Result<()> {
        match self.execute_command(ProxyRequest::Bootstrap {
            options: options.clone(),
            payload: payload.to_vec(),
        })? {
            ProxyResponse::Bootstrap => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn apply_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        match self.execute_command(ProxyRequest::ApplyPinStrapping {
            strapping_name: strapping_name.to_string(),
        })? {
            ProxyResponse::ApplyPinStrapping => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn remove_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        match self.execute_command(ProxyRequest::RemovePinStrapping {
            strapping_name: strapping_name.to_string(),
        })? {
            ProxyResponse::RemovePinStrapping => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn apply_default_configuration_with_strap(&self, strapping_name: &str) -> Result<()> {
        match self.execute_command(ProxyRequest::ApplyDefaultConfigurationWithStrapping {
            strapping_name: strapping_name.to_string(),
        })? {
            ProxyResponse::ApplyDefaultConfigurationWithStrapping => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl Transport for Proxy {
    fn capabilities(&self) -> Result<Capabilities> {
        match self.inner.execute_command(Request::GetCapabilities)? {
            Response::GetCapabilities(capabilities) => Ok(capabilities.add(Capability::PROXY)),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn apply_default_configuration(&self) -> Result<()> {
        match self
            .inner
            .execute_command(Request::ApplyDefaultConfiguration)?
        {
            Response::ApplyDefaultConfiguration => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    // Create SPI Target instance, or return one from a cache of previously created instances.
    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        Ok(Rc::new(spi::ProxySpi::open(self, instance)?))
    }

    // Create I2C Target instance, or return one from a cache of previously created instances.
    fn i2c(&self, instance: &str) -> Result<Rc<dyn Bus>> {
        Ok(Rc::new(i2c::ProxyI2c::open(self, instance)?))
    }

    // Create Uart instance, or return one from a cache of previously created instances.
    fn uart(&self, instance_name: &str) -> Result<Rc<dyn Uart>> {
        if let Some(instance) = self.inner.uarts.borrow().get(instance_name) {
            return Ok(Rc::clone(&instance.uart));
        }

        // All `Uart` instances that we create via proxy supports non-blocking.
        // This allows us to control whether UART is blocking or not by controlling if
        // `pipe_receiver` is blocking.
        let Response::Uart(UartResponse::RegisterNonblockingRead { channel }) =
            self.inner.execute_command(Request::Uart {
                id: instance_name.to_owned(),
                command: UartRequest::RegisterNonblockingRead,
            })?
        else {
            bail!(ProxyError::UnexpectedReply())
        };

        let instance: Rc<dyn Uart> = Rc::new(uart::ProxyUart::open(self, instance_name)?);
        let (pipe_receiver, pipe_sender) = tokio::io::simplex(65536);

        self.inner
            .uart_channel_map
            .borrow_mut()
            .insert(channel, instance_name.to_owned());
        self.inner.uarts.borrow_mut().insert(
            instance_name.to_owned(),
            UartRecord {
                uart: Rc::clone(&instance),
                pipe_sender,
                pipe_receiver,
            },
        );
        Ok(instance)
    }

    // Create GpioPin instance, or return one from a cache of previously created instances.
    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(Rc::new(gpio::ProxyGpioPin::open(self, pinname)?))
    }

    // Create GpioMonitoring instance.
    fn gpio_monitoring(&self) -> Result<Rc<dyn GpioMonitoring>> {
        Ok(Rc::new(gpio::GpioMonitoringImpl::new(self)?))
    }

    // Create GpioBitbanging instance.
    fn gpio_bitbanging(&self) -> Result<Rc<dyn GpioBitbanging>> {
        Ok(Rc::new(gpio::GpioBitbangingImpl::new(self)?))
    }

    // Create Emulator instance, or return one from a cache of previously created instances.
    fn emulator(&self) -> Result<Rc<dyn Emulator>> {
        Ok(Rc::new(emu::ProxyEmu::open(self)?))
    }

    // Create ProxyOps instance.
    fn proxy_ops(&self) -> Result<Rc<dyn ProxyOps>> {
        Ok(Rc::new(ProxyOpsImpl::new(self)?))
    }
}
