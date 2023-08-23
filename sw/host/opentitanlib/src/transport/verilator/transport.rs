// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Context, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use serde_annotate::Annotate;
use std::any::Any;
use std::cell::RefCell;
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::io::gpio::{GpioError, GpioPin};
use crate::io::io_mapper::IoMapper;
use crate::io::uart::Uart;
use crate::transport::verilator::gpio::{GpioInner, VerilatorGpioPin};
use crate::transport::verilator::subprocess::{Options, Subprocess};
use crate::transport::verilator::uart::VerilatorUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
use crate::util::parse_int::ParseInt;

pub(crate) struct Inner {
    uart: Option<Rc<dyn Uart>>,
    pub gpio: GpioInner,
}

/// Represents the verilator transport object.
pub struct Verilator {
    subprocess: Option<Subprocess>,
    pub uart_file: String,
    pub spi_file: String,
    pub gpio_read_file: String,
    pub gpio_write_file: String,

    inner: Rc<RefCell<Inner>>,
    io_mapper: Rc<IoMapper>,
}

impl Verilator {
    /// Creates a verilator subprocess-hosting transport from `options`.
    pub fn from_options(options: Options, io_mapper: Rc<IoMapper>) -> Result<Self> {
        static UART: Lazy<Regex> =
            Lazy::new(|| Regex::new("UART: Created ([^ ]+) for uart0").unwrap());
        static SPI: Lazy<Regex> =
            Lazy::new(|| Regex::new("SPI: Created ([^ ]+) for spi0").unwrap());
        static GPIO_RD: Lazy<Regex> = Lazy::new(|| {
            Regex::new(r"GPIO: FIFO pipes created at ([^ ]+) \(read\) and [^ ]+ \(write\) for 32-bit wide GPIO.").unwrap()
        });
        static GPIO_WR: Lazy<Regex> = Lazy::new(|| {
            Regex::new(r"GPIO: FIFO pipes created at [^ ]+ \(read\) and ([^ ]+) \(write\) for 32-bit wide GPIO.").unwrap()
        });

        let deadline = Instant::now() + options.timeout;
        let subprocess = Subprocess::from_options(options)?;
        let gpio_rd = subprocess.find(&GPIO_RD, deadline)?;
        let gpio_wr = subprocess.find(&GPIO_WR, deadline)?;
        let uart = subprocess.find(&UART, deadline)?;
        let spi = subprocess.find(&SPI, deadline)?;

        log::info!("Verilator started with the following interfaces:");
        log::info!("gpio_read = {}", gpio_rd);
        log::info!("gpio_write = {}", gpio_wr);
        let gpio = GpioInner::new(&gpio_rd, &gpio_wr)?;
        log::info!("uart = {}", uart);
        log::info!("spi = {}", spi);

        Ok(Verilator {
            subprocess: Some(subprocess),
            uart_file: uart,
            spi_file: spi,
            gpio_read_file: gpio_rd,
            gpio_write_file: gpio_wr,
            inner: Rc::new(RefCell::new(Inner { uart: None, gpio })),
            io_mapper,
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
        Ok(Capabilities::new(Capability::UART | Capability::GPIO))
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        let instance = self.io_mapper.resolve_uart(instance);

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

    fn gpio_pin(&self, instance: &str) -> Result<Rc<dyn GpioPin>> {
        let resolved_pin = self.io_mapper.resolve_pin(instance);

        let pin =
            u8::from_str(&resolved_pin).with_context(|| format!("can't convert {instance:?}"))?;
        ensure!(pin < 32 || pin == 255, GpioError::InvalidPinNumber(pin));
        let mut inner = self.inner.borrow_mut();
        Ok(Rc::clone(inner.gpio.pins.entry(pin).or_insert_with(|| {
            VerilatorGpioPin::new(Rc::clone(&self.inner), pin)
        })))
    }

    fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Annotate>>> {
        if let Some(watch) = action.downcast_ref::<Watch>() {
            let subprocess = self.subprocess.as_ref().unwrap();
            let deadline = Instant::now() + watch.timeout.unwrap_or(Watch::FOREVER);
            let result = subprocess.find(&watch.regex, deadline)?;
            Ok(Some(Box::new(WatchResponse { result })))
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }
}

/// Watch verilator's stdout for a expression or timeout.
pub struct Watch {
    pub regex: Regex,
    pub timeout: Option<Duration>,
}

impl Watch {
    // Using Duration::MAX causes an overflow when calculating a deadline.
    // We use 100 years -- although it isn't "forever", it is longer than
    // any invocation of opentitantool.
    pub const FOREVER: Duration = Duration::from_secs(100 * 365 * 86400);
}

#[derive(serde::Serialize, Debug)]
pub struct WatchResponse {
    pub result: String,
}
