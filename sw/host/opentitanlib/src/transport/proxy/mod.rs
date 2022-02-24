// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::io;
use std::io::{BufReader, BufWriter, ErrorKind, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::rc::Rc;
use thiserror::Error;

use crate::bail;
use crate::io::gpio::GpioPin;
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::proxy::protocol;
use crate::proxy::protocol::Message;
use crate::transport::{
    Capabilities, Capability, Result, Transport, TransportError, WrapInTransportError,
};

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

/// Implementation of the Transport trait backed by connection to a remote OpenTitan tool
/// session process.
pub struct Proxy {
    inner: Rc<Inner>,
}

impl Proxy {
    /// Establish connection with a running session process.
    pub fn open(host: Option<&str>, port: u16) -> anyhow::Result<Self> {
        let host = host.unwrap_or("localhost");
        let addr = ToSocketAddrs::to_socket_addrs(&(host, port))
            .map_err(|e| TransportError::ProxyLookupError(host.to_string(), e.to_string()))?
            .next()
            .unwrap();
        let conn = TcpStream::connect(addr)
            .map_err(|e| TransportError::ProxyConnectError(addr.to_string(), e.to_string()))?;
        Ok(Self {
            inner: Rc::new(Inner {
                reader: RefCell::new(BufReader::new(conn.try_clone()?)),
                writer: RefCell::new(BufWriter::new(conn)),
            }),
        })
    }
}

struct Inner {
    reader: RefCell<BufReader<TcpStream>>,
    writer: RefCell<BufWriter<TcpStream>>,
}

impl Inner {
    /// Helper method for sending one JSON request and receiving the response.  Called as part
    /// of the implementation of every method of the sub-traits (gpio, uart, spi, i2c).
    fn execute_command(&self, req: protocol::Request) -> Result<protocol::Response> {
        self.send_json_request(req).wrap(ProxyError::JsonEncoding)?;
        match self.recv_json_response().wrap(ProxyError::JsonDecoding)? {
            Message::Res(res) => res,
            _ => bail!(ProxyError::UnexpectedReply()),
        }
    }

    /// Send a one-line JSON encoded requests, terminated with one newline.
    fn send_json_request(&self, req: protocol::Request) -> anyhow::Result<()> {
        let mut conn = self.writer.borrow_mut();
        serde_json::to_writer(&mut *conn, &Message::Req(req))?;
        conn.write(&[b'\n'])?;
        conn.flush()?;
        Ok(())
    }

    /// Receive until newline, and decode one JSON response.
    fn recv_json_response(&self) -> anyhow::Result<Message> {
        let mut conn = self.reader.borrow_mut();
        let mut buf = Vec::new();
        let mut idx: usize = 0;
        loop {
            buf.resize(idx + 2048, 0);
            let rc = conn.read(&mut buf[idx..])?;
            if rc == 0 {
                anyhow::bail!(io::Error::new(ErrorKind::UnexpectedEof, "Truncated JSON"))
            }
            idx += rc;
            if buf[idx - 1] == b'\n' {
                break;
            }
        }
        Ok(serde_json::from_slice::<Message>(&buf[..idx - 1])?)
    }
}

impl Transport for Proxy {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::UART | Capability::GPIO | Capability::SPI | Capability::I2C)
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
    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        Ok(Rc::new(uart::ProxyUart::open(self, instance)?))
    }

    // Create GpioPin instance, or return one from a cache of previously created instances.
    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(Rc::new(gpio::ProxyGpioPin::open(self, pinname)?))
    }
}
