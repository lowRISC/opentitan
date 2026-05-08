// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::rc::Rc;

use anyhow::Result;
use serialport::SerialPortType;

use opentitanlib::backend::{Backend, BackendOpts, define_interface};
use opentitanlib::io::gpio::{GpioPin, PinMode};
use opentitanlib::io::spi::Target;
use opentitanlib::io::uart::flow::SoftwareFlowControl;
use opentitanlib::io::uart::serial::SerialPortUart;
use opentitanlib::io::uart::{Uart, UartError};
use opentitanlib::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
use opentitanlib::util::fs::builtin_file;
use opentitanlib::util::parse_int::ParseInt;

pub mod chip;
pub mod gpio;
pub mod spi;

use chip::{Chip, Ft4232hq};

#[derive(Default)]
struct Inner {
    spi: Option<Rc<dyn Target>>,
    gpio: HashMap<String, Rc<dyn GpioPin>>,
    uart: HashMap<u32, Rc<dyn Uart>>,
}

pub struct Ftdi<C: Chip> {
    pub(crate) ftdi_interfaces:
        Rc<HashMap<ftdi::Interface, ftdi_embedded_hal::FtHal<ftdi::Device>>>,
    inner: RefCell<Inner>,
    phantom: std::marker::PhantomData<C>,
}

impl<C: Chip> Ftdi<C> {
    pub fn new() -> anyhow::Result<Self> {
        let mut ftdi_interfaces = HashMap::new();
        for interface in C::INTERFACES {
            let device = ftdi::find_by_vid_pid(C::VENDOR_ID, C::PRODUCT_ID)
                .interface(*interface)
                .open()?;
            ftdi_interfaces.insert(
                *interface,
                ftdi_embedded_hal::FtHal::init_freq(device, 8_000_000)?,
            );
        }

        let ftdi_dev = Ftdi {
            ftdi_interfaces: Rc::new(ftdi_interfaces),
            inner: RefCell::default(),
            phantom: std::marker::PhantomData,
        };
        Ok(ftdi_dev)
    }

    fn open_uart(&self, instance: u32) -> Result<SoftwareFlowControl<SerialPortUart>> {
        let mut ports = serialport::available_ports()
            .map_err(|e| UartError::EnumerationError(e.to_string()))?;

        ports.retain(|port| {
            if let SerialPortType::UsbPort(info) = &port.port_type
                && info.vid == C::VENDOR_ID
                && info.pid == C::PRODUCT_ID
            {
                return true;
            }
            false
        });

        let port = ports.get(instance as usize).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        })?;

        Ok(SoftwareFlowControl::new(SerialPortUart::open(
            &port.port_name,
            C::UART_BAUD,
        )?))
    }
}

impl<C: Chip> Transport for Ftdi<C> {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(
            Capability::SPI | Capability::GPIO | Capability::UART | Capability::UART_NONBLOCKING,
        ))
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        let mut inner = self.inner.borrow_mut();
        let instance = u32::from_str(instance).ok().ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        })?;
        let uart = match inner.uart.entry(instance) {
            Entry::Vacant(v) => v.insert(Rc::new(self.open_uart(instance)?)).clone(),
            Entry::Occupied(o) => o.get().clone(),
        };
        Ok(uart)
    }

    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        let mut inner = self.inner.borrow_mut();
        Ok(match inner.gpio.entry(pinname.to_string()) {
            Entry::Vacant(v) => v
                .insert(Rc::new(gpio::Pin::open::<C>(
                    &self.ftdi_interfaces,
                    pinname.to_string(),
                )?))
                .clone(),
            Entry::Occupied(o) => o.get().clone(),
        })
    }

    fn spi(&self, _instance: &str) -> Result<Rc<dyn Target>> {
        let spi_cs = gpio::Pin::open::<C>(&self.ftdi_interfaces, "bdbus3".to_string())?;
        spi_cs.set_mode(PinMode::PushPull)?;
        let mut inner = self.inner.borrow_mut();
        if inner.spi.is_none() {
            inner.spi = Some(Rc::new(spi::Spi::open(&self.ftdi_interfaces, spi_cs)?));
        }
        Ok(inner.spi.as_ref().unwrap().clone())
    }
}

struct FtdiBackend<C>(C);

impl<C: Chip + 'static> Backend for FtdiBackend<C> {
    type Opts = ();

    fn create_transport(_: &BackendOpts, _: &()) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Ftdi::<C>::new()?))
    }
}

define_interface!(
    "ftdi",
    FtdiBackend<Ft4232hq>,
    "/__builtin__/opentitan_ftdi_voyager.json5"
);
builtin_file!(
    "opentitan_ftdi_voyager.json5",
    include_str!("../config/opentitan_ftdi_voyager.json5")
);
