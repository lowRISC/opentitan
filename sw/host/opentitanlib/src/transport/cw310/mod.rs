// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;

use crate::io::gpio::Gpio;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{Capabilities, Capability, Transport, TransportError};

pub mod gpio;
pub mod spi;
pub mod uart;
pub mod usb;

#[derive(Default)]
struct Inner {
    spi: Option<Rc<dyn Target>>,
    gpio: Option<Rc<dyn Gpio>>,
    uart: HashMap<u32, Rc<dyn Uart>>,
}

pub struct CW310 {
    device: Rc<RefCell<usb::Backend>>,
    inner: RefCell<Inner>,
}

impl CW310 {
    // Pins needed for reset & bootstrap on the CW310 board.
    const PIN_SRST: &'static str = "USB_A18";
    const PIN_BOOTSTRAP: &'static str = "USB_A16";
    // Pins needed for SPI on the CW310 board.
    const PIN_CLK: &'static str = "USB_SPI_SCK";
    const PIN_SDI: &'static str = "USB_SPI_COPI";
    const PIN_SDO: &'static str = "USB_SPI_CIPO";
    const PIN_CS: &'static str = "USB_SPI_CS";
    const PIN_JTAG: &'static str = "USB_A19";

    pub fn new(
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: Option<String>,
    ) -> Result<Self> {
        let board = CW310 {
            device: Rc::new(RefCell::new(usb::Backend::new(
                usb_vid, usb_pid, usb_serial,
            )?)),
            inner: RefCell::default(),
        };
        board.init_direction()?;
        Ok(board)
    }

    // Initialize the IO direction of some basic pins on the board.
    fn init_direction(&self) -> Result<()> {
        let device = self.device.borrow();
        device.pin_set_output(Self::PIN_SRST, true)?;
        device.pin_set_output(Self::PIN_JTAG, true)?;
        device.pin_set_output(Self::PIN_BOOTSTRAP, true)?;
        Ok(())
    }
}

impl Transport for CW310 {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(
            Capability::SPI | Capability::GPIO | Capability::UART | Capability::FPGA_PROGRAM,
        )
    }

    fn uart(&self, instance: u32) -> Result<Rc<dyn Uart>> {
        let mut inner = self.inner.borrow_mut();
        let uart = match inner.uart.entry(instance) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(uart::CW310Uart::open(
                    Rc::clone(&self.device),
                    instance,
                )?));
                Rc::clone(u)
            }
            Entry::Occupied(o) => Rc::clone(o.get()),
        };
        Ok(uart)
    }

    fn gpio(&self) -> Result<Rc<dyn Gpio>> {
        let mut inner = self.inner.borrow_mut();
        if inner.gpio.is_none() {
            inner.gpio = Some(Rc::new(gpio::CW310Gpio::open(Rc::clone(&self.device))?));
        }
        Ok(Rc::clone(inner.gpio.as_ref().unwrap()))
    }

    fn spi(&self, instance: u32) -> Result<Rc<dyn Target>> {
        ensure!(
            instance == 0,
            TransportError::InvalidInstance("spi", instance)
        );
        let mut inner = self.inner.borrow_mut();
        if inner.spi.is_none() {
            inner.spi = Some(Rc::new(spi::CW310Spi::open(Rc::clone(&self.device))?));
        }
        Ok(Rc::clone(inner.spi.as_ref().unwrap()))
    }

    fn fpga_program(&self, bitstream: &[u8]) -> Result<()> {
        let usb = self.device.borrow();
        usb.spi1_enable(false)?;
        usb.pin_set_state(CW310::PIN_JTAG, true)?;
        usb.fpga_program(bitstream)
    }
}
