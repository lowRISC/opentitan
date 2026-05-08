// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::io::ErrorKind;
use std::rc::Rc;
use std::sync::Arc;
use std::task::Waker;

use anyhow::{Context, Result, bail};
use clap::Args;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::Mutex;
use tokio::task::AbortHandle;

use opentitanlib::backend::{Backend, BackendOpts, define_interface};
use opentitanlib::bootstrap::BootstrapOptions;
use opentitanlib::impl_serializable_error;
use opentitanlib::io::console::Buffered;
use opentitanlib::io::emu::Emulator;
use opentitanlib::io::gpio::{GpioBitbanging, GpioMonitoring, GpioPin};
use opentitanlib::io::i2c::Bus;
use opentitanlib::io::spi::Target;
use opentitanlib::io::uart::Uart;
use opentitanlib::transport::{
    Capabilities, Capability, FpgaOps, ProgressIndicator, ProxyOps, Transport, TransportError,
};
use opentitanlib::util::serializable_error::SerializedError;
use ot_proxy_proto::{
    FgpaResponse, FpgaRequest, Message, ProxyRequest, ProxyResponse, Request, Response,
    UartRequest, UartResponse,
};

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
        let _enter_guard = opentitanlib::util::runtime().enter();

        let host = host.unwrap_or("localhost");
        let conn = opentitanlib::util::runtime::block_on(TcpStream::connect(&(host, port)))
            .map_err(|e| TransportError::ProxyConnectError(host.to_string(), e.to_string()))?;
        // Disable Nagle's algorithm to ensure reasonable communication latency.
        conn.set_nodelay(true)?;

        // Launch a new task for receiver messages.
        // We do not just poll messages when we have a pending request, as there are asynchronous
        // messages that we want to handle ASAP.
        let (conn_rx, conn_tx) = conn.into_split();
        let (resp_send, resp_recv) = tokio::sync::mpsc::channel(32);
        let wakers = Arc::new(std::sync::Mutex::new(Vec::new()));

        let wakers_clone = wakers.clone();
        let recv_task = tokio::task::spawn(async move {
            if let Err(err) = Self::recv_messages(conn_rx, resp_send, wakers_clone).await {
                log::warn!("Receving failed with {err}");
            }
        });

        Ok(Self {
            inner: Rc::new(Inner {
                conn_tx: Mutex::new(conn_tx),
                resp_recv: Mutex::new(resp_recv),
                uarts: RefCell::new(HashMap::new()),
                wakers,
                recv_task: recv_task.abort_handle(),
            }),
        })
    }

    async fn recv_messages(
        conn_rx: OwnedReadHalf,
        resp_send: tokio::sync::mpsc::Sender<Result<Response, SerializedError>>,
        wakers: Arc<std::sync::Mutex<Vec<Option<Waker>>>>,
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
            match msg {
                Message::Res(resp) => {
                    resp_send.send(resp).await.context("sender closed")?;
                }
                Message::Wake { id, triggered } => {
                    if let Some(waker) = Inner::get_waker_by_id(&wakers, id)
                        && triggered
                    {
                        waker.wake();
                    }
                }
                _ => bail!(ProxyError::UnexpectedReply()),
            }
        }
    }
}

struct Inner {
    conn_tx: Mutex<OwnedWriteHalf>,
    resp_recv: Mutex<tokio::sync::mpsc::Receiver<Result<Response, SerializedError>>>,
    uarts: RefCell<HashMap<String, Rc<dyn Uart>>>,
    pub wakers: Arc<std::sync::Mutex<Vec<Option<Waker>>>>,
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
        opentitanlib::util::runtime::block_on(async {
            self.send_json_request(req).await.context("json encoding")?;
            Ok(self
                .resp_recv
                .lock()
                .await
                .recv()
                .await
                .context("dequeueing")??)
        })
    }

    // Convenience method for issuing Proxy-only commands via proxy protocol.
    fn execute_proxy_command(&self, command: ProxyRequest) -> Result<ProxyResponse> {
        match self.execute_command(Request::Proxy(command))? {
            Response::Proxy(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Send a one-line JSON encoded requests, terminated with one newline.
    async fn send_json_request(&self, req: Request) -> Result<()> {
        let mut vec = serde_json::to_vec(&Message::Req(req))?;
        vec.push(b'\n');

        let mut conn = self.conn_tx.lock().await;
        conn.write_all(&vec).await?;
        conn.flush().await?;
        Ok(())
    }

    fn allocate_wake_id(&self, waker: Waker) -> u32 {
        let mut wakers = self.wakers.lock().unwrap();

        let none_index = wakers.iter().position(|x| x.is_none());
        if let Some(index) = none_index {
            wakers[index] = Some(waker);
            index as u32
        } else {
            let index = wakers.len();
            wakers.push(Some(waker));
            index as u32
        }
    }

    fn get_waker_by_id(wakers: &std::sync::Mutex<Vec<Option<Waker>>>, id: u32) -> Option<Waker> {
        let mut wakers = wakers.lock().unwrap();

        if id as usize >= wakers.len() {
            return None;
        }

        let waker = wakers[id as usize].take();

        while let Some(None) = wakers.last() {
            wakers.pop();
        }

        waker
    }
}

impl FpgaOps for Proxy {
    fn load_bitstream(&self, bitstream: &[u8], _progress: &dyn ProgressIndicator) -> Result<()> {
        match self
            .inner
            .execute_command(Request::Fpga(FpgaRequest::LoadBitstream {
                bitstream: bitstream.to_owned(),
            }))? {
            Response::Fpga(FgpaResponse::LoadBitstream) => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn clear_bitstream(&self) -> Result<()> {
        match self
            .inner
            .execute_command(Request::Fpga(FpgaRequest::ClearBitstream))?
        {
            Response::Fpga(FgpaResponse::ClearBitstream) => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }
}

impl ProxyOps for Proxy {
    fn provides_map(&self) -> Result<HashMap<String, String>> {
        match self
            .inner
            .execute_proxy_command(ProxyRequest::Provides {})?
        {
            ProxyResponse::Provides { provides_map } => Ok(provides_map),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn bootstrap(&self, options: &BootstrapOptions, payload: &[u8]) -> Result<()> {
        match self.inner.execute_proxy_command(ProxyRequest::Bootstrap {
            options: options.clone(),
            payload: payload.to_vec(),
        })? {
            ProxyResponse::Bootstrap => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn apply_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        match self
            .inner
            .execute_proxy_command(ProxyRequest::ApplyPinStrapping {
                strapping_name: strapping_name.to_string(),
            })? {
            ProxyResponse::ApplyPinStrapping => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn remove_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        match self
            .inner
            .execute_proxy_command(ProxyRequest::RemovePinStrapping {
                strapping_name: strapping_name.to_string(),
            })? {
            ProxyResponse::RemovePinStrapping => Ok(()),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn apply_default_configuration_with_strap(&self, strapping_name: &str) -> Result<()> {
        match self.inner.execute_proxy_command(
            ProxyRequest::ApplyDefaultConfigurationWithStrapping {
                strapping_name: strapping_name.to_string(),
            },
        )? {
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
            return Ok(instance.clone());
        }

        let instance: Rc<dyn Uart> =
            Rc::new(Buffered::new(uart::ProxyUart::open(self, instance_name)?));

        // Send an initial message to register the intent on receiving messages.
        let Response::Uart(UartResponse::Initialize) =
            self.inner.execute_command(Request::Uart {
                id: instance_name.to_owned(),
                command: UartRequest::Initialize,
            })?
        else {
            bail!(ProxyError::UnexpectedReply())
        };

        self.inner
            .uarts
            .borrow_mut()
            .insert(instance_name.to_owned(), instance.clone());
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
    fn emulator(&self) -> Result<&dyn Emulator> {
        Ok(self)
    }

    fn fpga_ops(&self) -> Result<&dyn FpgaOps> {
        Ok(self)
    }

    // Create ProxyOps instance.
    fn proxy_ops(&self) -> Result<&dyn ProxyOps> {
        Ok(self)
    }
}

#[derive(Debug, Args)]
pub struct ProxyOpts {
    #[arg(long)]
    proxy: Option<String>,
    #[arg(long, default_value = "9900")]
    port: u16,
}

struct ProxyBackend;

impl Backend for ProxyBackend {
    type Opts = ProxyOpts;

    fn create_transport(_: &BackendOpts, args: &ProxyOpts) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Proxy::open(args.proxy.as_deref(), args.port)?))
    }
}

define_interface!("proxy", ProxyBackend);
