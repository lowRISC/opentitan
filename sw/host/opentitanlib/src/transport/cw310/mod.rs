// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use erased_serde::Serialize;
use serialport::SerialPortType;
use std::any::Any;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ensure;
use crate::io::gpio::GpioPin;
use crate::io::spi::Target;
use crate::io::uart::{Uart, UartError};
use crate::transport::{
    Capabilities, Capability, Result, Transport, TransportError, TransportInterfaceType,
    WrapInTransportError,
};
use crate::transport::common::uart::SerialPortUart;
use crate::util::parse_int::ParseInt;

pub mod gpio;
pub mod spi;
pub mod usb;

#[derive(Default)]
struct Inner {
    spi: Option<Rc<dyn Target>>,
    gpio: HashMap<String, Rc<dyn GpioPin>>,
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
        usb_serial: Option<&str>,
    ) -> anyhow::Result<Self> {
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
    fn init_direction(&self) -> anyhow::Result<()> {
        let device = self.device.borrow();
        device.pin_set_output(Self::PIN_SRST, true)?;
        device.pin_set_output(Self::PIN_JTAG, true)?;
        device.pin_set_output(Self::PIN_BOOTSTRAP, true)?;
        Ok(())
    }

    fn open_uart(&self, instance: u32) -> Result<SerialPortUart> {
        let usb = self.device.borrow();
        let serial_number = usb.get_serial_number();

        let mut ports = serialport::available_ports().wrap(UartError::EnumerationError)?;
        ports.retain(|port| {
            if let SerialPortType::UsbPort(info) = &port.port_type {
                if info.serial_number.as_deref() == Some(serial_number) {
                    return true;
                }
            }
            false
        });
        // The CW board seems to have the last port connected as OpenTitan UART 0.
        // Reverse the sort order so the last port will be instance 0.
        ports.sort_by(|a, b| b.port_name.cmp(&a.port_name));

        let port = ports.get(instance as usize).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        })?;
        SerialPortUart::open(&port.port_name)
    }
}

impl Transport for CW310 {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::SPI | Capability::GPIO | Capability::UART)
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        let mut inner = self.inner.borrow_mut();
        let instance = u32::from_str(instance).ok().ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        })?;
        let uart = match inner.uart.entry(instance) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(self.open_uart(
                    instance,
                )?));
                Rc::clone(u)
            }
            Entry::Occupied(o) => Rc::clone(o.get()),
        };
        Ok(uart)
    }

    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        let mut inner = self.inner.borrow_mut();
        Ok(match inner.gpio.entry(pinname.to_string()) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(gpio::CW310GpioPin::open(
                    Rc::clone(&self.device),
                    pinname.to_string(),
                )?));
                Rc::clone(u)
            }
            Entry::Occupied(o) => Rc::clone(o.get()),
        })
    }

    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        ensure!(
            instance == "0",
            TransportError::InvalidInstance(TransportInterfaceType::Spi, instance.to_string())
        );
        let mut inner = self.inner.borrow_mut();
        if inner.spi.is_none() {
            inner.spi = Some(Rc::new(spi::CW310Spi::open(Rc::clone(&self.device))?));
        }
        Ok(Rc::clone(inner.spi.as_ref().unwrap()))
    }

    fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Serialize>>> {
        if let Some(fpga_program) = action.downcast_ref::<FpgaProgram>() {
            let usb = self.device.borrow();
            usb.spi1_enable(false)?;
            usb.pin_set_state(CW310::PIN_JTAG, true)?;
            usb.fpga_program(&fpga_program.bitstream)?;
            Ok(None)
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }
}

/// Command for Transport::dispatch().
pub struct FpgaProgram {
    pub bitstream: Vec<u8>,
}
