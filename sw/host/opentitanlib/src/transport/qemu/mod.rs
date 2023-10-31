#![allow(unused)]

use anyhow::{bail, ensure, Context, Result};
use once_cell::sync::Lazy;
use std::any::Any;
use std::cell::{Cell, RefCell};
use std::io::{self, ErrorKind, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::rc::Rc;
use std::thread;
use std::time::{Duration, Instant};

use crate::io::spi::Target;
//use crate::transport::common::fpga::{ClearBitstream, FpgaProgram};
//use crate::transport::common::uart::SerialPortUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
//use crate::util::parse_int::ParseInt;

pub mod spi;

pub struct Inner {
    spi: Option<Rc<dyn Target>>,
    stream: TcpStream,
}

impl Inner {
    fn new(stream: TcpStream) -> Self {
        Self {
            spi: None,
            stream: stream
        }
    }
}

pub struct QEMU {
    inner: Rc<RefCell<Inner>>,
}

impl QEMU {
    const POLL_DELAY: Duration = Duration::from_millis(250);
    const CONN_DELAY: Duration = Duration::from_secs(2);

    pub fn new() -> anyhow::Result<Self> {
        let addr = format!("localhost:{}", 8004);
        let stream = Self::wait_for_socket(addr, QEMU::CONN_DELAY)
            .context("failed to connect to QEMU SPI_device socket")?;
        stream.set_read_timeout(Some(QEMU::POLL_DELAY))?;
        stream.set_write_timeout(Some(QEMU::POLL_DELAY))?;
        let inner = Inner::new(stream);
        let board = Self {
            inner: Rc::new(RefCell::new(inner)),
        };
        Ok(board)
    }

    /// Poll `addr` until it is bound and a socket can connect.
    fn wait_for_socket<A: ToSocketAddrs>(addr: A, timeout: Duration) -> io::Result<TcpStream> {
        let start = Instant::now();
        loop {
            log::info!("Attempting to make tcp connection...");
            match TcpStream::connect(&addr) {
                // This is the error for addresses that aren't bound
                Err(e) if e.kind() == ErrorKind::ConnectionRefused => (),
                // This is error has been observed in CQ.
                Err(e) if e.kind() == ErrorKind::AddrNotAvailable => {
                    log::warn!("Got ErrorKind::AddrInUse on client socket, odd...");
                }
                // All other errors (and `Ok`s) we want to know about
                Err(e) => {
                    log::warn!("Error: {:?}", e.kind());

                    return Err(e);
                }
                socket => {
                    log::info!("Connected");
                    return socket 
                }
            }

            // Delay between loops if there's enough time before timeout.
            if start.elapsed() + Self::POLL_DELAY < timeout {
                thread::sleep(Self::POLL_DELAY);
            } else {
                log::warn!("timeout");
                return Err(ErrorKind::TimedOut.into());
            }
        }
    }

}

impl Transport for QEMU {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(Capability::SPI))
    }

    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        ensure!(
            instance == "0",
            TransportError::InvalidInstance(TransportInterfaceType::Spi, instance.to_string())
        );
        if self.inner.borrow().spi.is_none() {
            self.inner.borrow_mut().spi =
                Some(Rc::new(spi::QEMUSpi::open(Rc::clone(&self.inner))?));
        }
        Ok(Rc::clone(self.inner.borrow().spi.as_ref().unwrap()))
    }
}
