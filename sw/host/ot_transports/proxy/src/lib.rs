// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::HashMap;
use std::io;
use std::io::{BufWriter, ErrorKind, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::rc::Rc;

use anyhow::{Context, Result, bail};
use clap::Args;
use serde::{Deserialize, Serialize};
use thiserror::Error;
use tokio::io::AsyncWriteExt;

use opentitanlib::backend::{Backend, BackendOpts, define_interface};
use opentitanlib::bootstrap::BootstrapOptions;
use opentitanlib::impl_serializable_error;
use opentitanlib::io::emu::Emulator;
use opentitanlib::io::gpio::{GpioBitbanging, GpioMonitoring, GpioPin};
use opentitanlib::io::i2c::Bus;
use opentitanlib::io::spi::Target;
use opentitanlib::io::uart::Uart;
use opentitanlib::transport::{Capabilities, Capability, ProxyOps, Transport, TransportError};
use ot_proxy_proto::{
    AsyncMessage, Message, ProxyRequest, ProxyResponse, Request, Response, UartRequest,
    UartResponse,
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
        let host = host.unwrap_or("localhost");
        let addr = ToSocketAddrs::to_socket_addrs(&(host, port))
            .map_err(|e| TransportError::ProxyLookupError(host.to_string(), e.to_string()))?
            .next()
            .unwrap();
        let conn = TcpStream::connect(addr)
            .map_err(|e| TransportError::ProxyConnectError(addr.to_string(), e.to_string()))?;
        Ok(Self {
            inner: Rc::new(Inner {
                conn: RefCell::new(conn),
                uarts: RefCell::new(HashMap::new()),
                uart_channel_map: RefCell::new(HashMap::new()),
                recv_buf: RefCell::new(Vec::new()),
            }),
        })
    }
}

struct UartRecord {
    pub uart: Rc<dyn Uart>,
    pub pipe_sender: tokio::io::WriteHalf<tokio::io::SimplexStream>,
    pub pipe_receiver: tokio::io::ReadHalf<tokio::io::SimplexStream>,
}

struct Inner {
    conn: RefCell<TcpStream>,
    pub uarts: RefCell<HashMap<String, UartRecord>>,
    uart_channel_map: RefCell<HashMap<u32, String>>,
    recv_buf: RefCell<Vec<u8>>,
}

impl Inner {
    /// Helper method for sending one JSON request and receiving the response.  Called as part
    /// of the implementation of every method of the sub-traits (gpio, uart, spi, i2c).
    fn execute_command(&self, req: Request) -> Result<Response> {
        self.send_json_request(req).context("json encoding")?;
        loop {
            match self.recv_json_response().context("json decoding")? {
                Message::Res(res) => match res {
                    Ok(value) => return Ok(value),
                    Err(e) => return Err(anyhow::Error::from(e)),
                },
                Message::Async { channel, msg } => self.process_async_data(channel, msg)?,
                _ => bail!(ProxyError::UnexpectedReply()),
            }
        }
    }

    // Convenience method for issuing Proxy-only commands via proxy protocol.
    fn execute_proxy_command(&self, command: ProxyRequest) -> Result<ProxyResponse> {
        match self.execute_command(Request::Proxy(command))? {
            Response::Proxy(resp) => Ok(resp),
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    fn poll_for_async_data(&self) -> Result<()> {
        self.recv_nonblocking()?;
        while let Some(msg) = self.dequeue_json_response()? {
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
                if let Some(uart_instance) = self.uart_channel_map.borrow().get(&channel)
                    && let Some(uart_record) = self.uarts.borrow_mut().get_mut(uart_instance)
                {
                    opentitanlib::util::runtime::block_on(async {
                        uart_record.pipe_sender.write_all(&data).await
                    })?;
                }
            }
        }
        Ok(())
    }

    /// Send a one-line JSON encoded requests, terminated with one newline.
    fn send_json_request(&self, req: Request) -> Result<()> {
        let conn: &mut std::net::TcpStream = &mut self.conn.borrow_mut();
        let mut writer = BufWriter::new(conn);
        serde_json::to_writer(&mut writer, &Message::Req(req))?;
        writer.write_all(b"\n")?;
        writer.flush()?;
        Ok(())
    }

    /// Decode one JSON response, possibly waiting for more network data.
    fn recv_json_response(&self) -> Result<Message> {
        if let Some(msg) = self.dequeue_json_response()? {
            return Ok(msg);
        }
        let mut conn = self.conn.borrow_mut();
        let mut buf = self.recv_buf.borrow_mut();
        let mut idx: usize = buf.len();
        loop {
            buf.resize(idx + 2048, 0);
            let rc = conn.read(&mut buf[idx..])?;
            if rc == 0 {
                anyhow::bail!(io::Error::new(
                    ErrorKind::UnexpectedEof,
                    "Server unexpectedly closed connection"
                ))
            }
            idx += rc;
            let Some(newline_pos) = buf[idx - rc..idx].iter().position(|b| *b == b'\n') else {
                continue;
            };
            let result = serde_json::from_slice::<Message>(&buf[..idx - rc + newline_pos])?;
            buf.resize(idx, 0u8);
            buf.drain(..idx - rc + newline_pos + 1);
            return Ok(result);
        }
    }

    fn recv_nonblocking(&self) -> Result<()> {
        let mut conn = self.conn.borrow_mut();
        conn.set_nonblocking(true)?;
        let mut buf = self.recv_buf.borrow_mut();
        let mut idx: usize = buf.len();
        loop {
            buf.resize(idx + 2048, 0);
            match conn.read(&mut buf[idx..]) {
                Ok(0) => {
                    anyhow::bail!(io::Error::new(
                        ErrorKind::UnexpectedEof,
                        "Server unexpectedly closed connection"
                    ))
                }
                Ok(rc) => idx += rc,
                Err(ref e) if e.kind() == ErrorKind::WouldBlock => break,
                Err(e) => anyhow::bail!(e),
            }
        }
        buf.resize(idx, 0);
        conn.set_nonblocking(false)?;
        Ok(())
    }

    fn dequeue_json_response(&self) -> Result<Option<Message>> {
        let mut buf = self.recv_buf.borrow_mut();
        let Some(newline_pos) = buf.iter().position(|b| *b == b'\n') else {
            return Ok(None);
        };
        let result = serde_json::from_slice::<Message>(&buf[..newline_pos])?;
        buf.drain(..newline_pos + 1);
        Ok(Some(result))
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
