// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use lazy_static::lazy_static;
use regex::Regex;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::Instant;

use crate::io::uart::Uart;
use crate::transport::verilator::subprocess::{Options, Subprocess};
use crate::transport::verilator::uart::VerilatorUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};

#[derive(Default)]
struct Inner {
    uart: Option<Rc<dyn Uart>>,
}

/// Represents the verilator transport object.
pub struct Verilator {
    subprocess: Option<Subprocess>,
    pub uart_file: String,
    pub spi_file: String,
    pub gpio_read_file: String,
    pub gpio_write_file: String,

    inner: RefCell<Inner>,
}

impl Verilator {
    /// Creates a verilator subprocess-hosting transport from [`options`].
    pub fn from_options(options: Options) -> Result<Self> {
        lazy_static! {
            static ref UART: Regex = Regex::new("UART: Created ([^ ]+) for uart0").unwrap();
            static ref SPI: Regex = Regex::new("SPI: Created ([^ ]+) for spi0").unwrap();
            static ref GPIO_RD: Regex =
                Regex::new(r#"GPIO: FIFO pipes created at ([^ ]+) \(read\) and [^ ]+ \(write\) for 32-bit wide GPIO."#).unwrap();
            static ref GPIO_WR: Regex =
                Regex::new(r#"GPIO: FIFO pipes created at [^ ]+ \(read\) and ([^ ]+) \(write\) for 32-bit wide GPIO."#).unwrap();
        }

        let deadline = Instant::now() + options.timeout;
        let mut subprocess = Subprocess::from_options(options)?;
        let gpio_rd = subprocess.find(&GPIO_RD, deadline)?;
        let gpio_wr = subprocess.find(&GPIO_WR, deadline)?;
        let uart = subprocess.find(&UART, deadline)?;
        let spi = subprocess.find(&SPI, deadline)?;

        log::info!("Verilator started with the following interaces:");
        log::info!("gpio_read = {}", gpio_rd);
        log::info!("gpio_write = {}", gpio_wr);
        log::info!("uart = {}", uart);
        log::info!("spi = {}", spi);
        Ok(Verilator {
            subprocess: Some(subprocess),
            uart_file: uart,
            spi_file: spi,
            gpio_read_file: gpio_rd,
            gpio_write_file: gpio_wr,
            inner: RefCell::default(),
        })
    }

    /// Shuts down the verilator subprocess.
    pub fn shutdown(&mut self) -> Result<()> {
        if let Some(mut subprocess) = self.subprocess.take() {
            subprocess.kill()
        } else {
            Ok(())
        }
    }
}

impl Drop for Verilator {
    fn drop(&mut self) {
        self.shutdown().expect("Kill verilator subprocess");
    }
}

impl Transport for Verilator {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(Capability::UART))
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        ensure!(
            instance == "0",
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        );
        let mut inner = self.inner.borrow_mut();
        if inner.uart.is_none() {
            inner.uart = Some(Rc::new(VerilatorUart::open(&self.uart_file)?));
        }
        Ok(Rc::clone(inner.uart.as_ref().unwrap()))
    }
}
