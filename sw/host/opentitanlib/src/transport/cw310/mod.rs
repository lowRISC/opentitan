// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use erased_serde::Serialize;
use serialport::SerialPortType;
use std::any::Any;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;

use crate::io::gpio::GpioPin;
use crate::io::spi::Target;
use crate::io::uart::{Uart, UartError};
use crate::transport::common::uart::SerialPortUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
use crate::util::parse_int::ParseInt;
use crate::util::rom_detect::{RomDetect, RomKind};

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
    uart_override: Vec<String>,
    inner: RefCell<Inner>,
}

impl CW310 {
    // Pins needed for SPI on the CW310 board.
    const PIN_CLK: &'static str = "USB_SPI_SCK";
    const PIN_SDI: &'static str = "USB_SPI_COPI";
    const PIN_SDO: &'static str = "USB_SPI_CIPO";
    const PIN_CS: &'static str = "USB_SPI_CS";
    // Pins needed for reset & bootstrap on the CW310 board.
    const PIN_TRST: &'static str = "USB_A13";
    const PIN_SRST: &'static str = "USB_A14";
    const PIN_SW_STRAP0: &'static str = "USB_A15";
    const PIN_SW_STRAP1: &'static str = "USB_A16";
    const PIN_SW_STRAP2: &'static str = "USB_A17";
    const PIN_TAP_STRAP0: &'static str = "USB_A18";
    const PIN_TAP_STRAP1: &'static str = "USB_A19";

    pub fn new(
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: Option<&str>,
        uart_override: &[&str],
    ) -> anyhow::Result<Self> {
        let board = CW310 {
            device: Rc::new(RefCell::new(usb::Backend::new(
                usb_vid, usb_pid, usb_serial,
            )?)),
            uart_override: uart_override.iter().map(|s| s.to_string()).collect(),
            inner: RefCell::default(),
        };
        board.init_pin_directions()?;
        board.init_pin_values()?;
        Ok(board)
    }

    // Initialize the IO direction of some basic pins on the board.
    fn init_pin_directions(&self) -> anyhow::Result<()> {
        let device = self.device.borrow();
        device.pin_set_output(Self::PIN_TRST, true)?;
        device.pin_set_output(Self::PIN_SRST, true)?;
        device.pin_set_output(Self::PIN_TAP_STRAP0, true)?;
        device.pin_set_output(Self::PIN_TAP_STRAP1, true)?;
        device.pin_set_output(Self::PIN_SW_STRAP0, true)?;
        device.pin_set_output(Self::PIN_SW_STRAP1, true)?;
        device.pin_set_output(Self::PIN_SW_STRAP2, true)?;
        Ok(())
    }

    // Initialize the values of the output pins on the board.
    fn init_pin_values(&self) -> anyhow::Result<()> {
        let device = self.device.borrow();
        device.pin_set_state(Self::PIN_TRST, true)?;
        device.pin_set_state(Self::PIN_SRST, true)?;
        device.pin_set_state(Self::PIN_TAP_STRAP0, false)?;
        device.pin_set_state(Self::PIN_TAP_STRAP1, true)?;
        device.pin_set_state(Self::PIN_SW_STRAP0, false)?;
        device.pin_set_state(Self::PIN_SW_STRAP1, false)?;
        device.pin_set_state(Self::PIN_SW_STRAP2, false)?;
        Ok(())
    }

    fn open_uart(&self, instance: u32) -> Result<SerialPortUart> {
        if self.uart_override.is_empty() {
            let usb = self.device.borrow();
            let serial_number = usb.get_serial_number();

            let mut ports = serialport::available_ports()
                .map_err(|e| UartError::EnumerationError(e.to_string()))?;
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
        } else {
            let instance = instance as usize;
            ensure!(
                instance < self.uart_override.len(),
                TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
            );
            SerialPortUart::open(&self.uart_override[instance])
        }
    }
}

impl Transport for CW310 {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(
            Capability::SPI | Capability::GPIO | Capability::UART,
        ))
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        let mut inner = self.inner.borrow_mut();
        let instance = u32::from_str(instance).ok().ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        })?;
        let uart = match inner.uart.entry(instance) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(self.open_uart(instance)?));
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
            // Open the console UART.  We do this first so we get the receiver
            // started and the uart buffering data for us.
            let uart = self.uart("0")?;
            if fpga_program.bitstream.starts_with(b"__skip__") {
                log::info!("Skip loading the __skip__ bitstream.");
                return Ok(None);
            }
            if let Some(rom_kind) = &fpga_program.rom_kind {
                let mut rd = RomDetect::new(
                    *rom_kind,
                    &fpga_program.bitstream,
                    Some(fpga_program.rom_timeout),
                )?;

                // Send a reset pulse so the ROM will print the FPGA version.
                let reset_pin = self.gpio_pin(Self::PIN_SRST)?;
                // Reset is active low, sleep, then drive high.
                reset_pin.write(false)?;
                std::thread::sleep(fpga_program.rom_reset_pulse);
                reset_pin.write(true)?;

                // Now read the uart until the ROM prints it's version.
                if rd.detect(&*uart)? {
                    log::info!("Already running the correct bitstream.  Skip loading bitstream.");
                    // If we're already running the right ROM+bitstream,
                    // then we can skip bootstrap.
                    return Ok(None);
                }
            }

            // Program the FPGA bitstream.
            log::info!("Programming the FPGA bitstream.");
            let usb = self.device.borrow();
            usb.spi1_enable(false)?;
            usb.fpga_program(
                &fpga_program.bitstream,
                fpga_program.progress.as_ref().map(Box::as_ref),
            )?;
            Ok(None)
        } else if let Some(_set_pll) = action.downcast_ref::<SetPll>() {
            const TARGET_FREQ: u32 = 100_000_000;
            let usb = self.device.borrow();
            usb.pll_enable(true)?;
            usb.pll_out_freq_set(1, TARGET_FREQ)?;
            usb.pll_out_freq_set(2, TARGET_FREQ)?;
            usb.pll_out_enable(0, false)?;
            usb.pll_out_enable(1, true)?;
            usb.pll_out_enable(2, false)?;
            usb.pll_write_defaults()?;
            Ok(None)
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }
}

/// Command for Transport::dispatch().
pub struct FpgaProgram<'a> {
    /// The bitstream content to load into the FPGA.
    pub bitstream: Vec<u8>,
    /// What type of ROM to expect.
    pub rom_kind: Option<RomKind>,
    /// How long of a reset pulse to send to the device.
    pub rom_reset_pulse: Duration,
    /// How long to wait for the ROM to print its type and version.
    pub rom_timeout: Duration,
    /// A progress function to provide user feedback.
    /// Will be called with the address and length of each chunk sent to the target device.
    pub progress: Option<Box<dyn Fn(u32, u32) -> () + 'a>>,
}

/// Command for Transport::dispatch().
pub struct SetPll {}
