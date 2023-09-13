// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use serde_annotate::Annotate;
use serialport::SerialPortType;
use std::any::Any;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;

use crate::io::gpio::{GpioPin, PinMode};
use crate::io::io_mapper::IoMapper;
use crate::io::jtag::{Jtag, JtagParams};
use crate::io::spi::Target;
use crate::io::uart::{Uart, UartError};
use crate::transport::common::fpga::{ClearBitstream, FpgaProgram};
use crate::transport::common::uart::SerialPortUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
use crate::util::openocd::OpenOcdServer;
use crate::util::parse_int::ParseInt;
use board::Board;

pub mod board;
pub mod gpio;
pub mod spi;
pub mod usb;

#[derive(Default)]
struct Inner {
    spi: Option<Rc<dyn Target>>,
    gpio: HashMap<String, Rc<dyn GpioPin>>,
    uart: HashMap<u32, Rc<dyn Uart>>,
    jtag: Option<Rc<dyn Jtag>>,
}

pub struct ChipWhisperer<B: Board> {
    pub(crate) device: Rc<RefCell<usb::Backend<B>>>,
    uart_override: Vec<String>,
    inner: RefCell<Inner>,
    io_mapper: Rc<IoMapper>,
}

impl<B: Board> ChipWhisperer<B> {
    pub fn new(
        io_mapper: Rc<IoMapper>,
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: Option<&str>,
        uart_override: &[&str],
    ) -> anyhow::Result<Self> {
        let board = ChipWhisperer {
            device: Rc::new(RefCell::new(usb::Backend::new(
                usb_vid, usb_pid, usb_serial,
            )?)),
            uart_override: uart_override.iter().map(|s| s.to_string()).collect(),
            inner: RefCell::default(),
            io_mapper,
        };
        board.init_pin_directions()?;
        board.init_pin_values()?;
        Ok(board)
    }

    // Initialize the IO direction of some basic pins on the board.
    fn init_pin_directions(&self) -> anyhow::Result<()> {
        let device = self.device.borrow();
        for pin in self.io_mapper.list_gpio_pins() {
            let config = self.io_mapper.pin_config(pin).unwrap();
            let mode = config.mode.unwrap_or(PinMode::PushPull);
            if mode == PinMode::PushPull {
                device.pin_set_output(pin, true)?;
            }
        }
        Ok(())
    }

    // Initialize the values of the output pins on the board.
    fn init_pin_values(&self) -> anyhow::Result<()> {
        let device = self.device.borrow();
        for pin in self.io_mapper.list_gpio_pins() {
            let config = self.io_mapper.pin_config(pin).unwrap();
            let mode = config.mode.unwrap_or(PinMode::PushPull);
            if mode != PinMode::Alternate {
                let level = config.level.unwrap_or(false);
                device.pin_set_state(pin, level)?;
            }
        }
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

impl<B: Board + 'static> Transport for ChipWhisperer<B> {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(
            Capability::SPI
                | Capability::GPIO
                | Capability::UART
                | Capability::UART_NONBLOCKING
                | Capability::JTAG,
        ))
    }

    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        let resolved = self.io_mapper.resolve_uart(instance);

        let mut inner = self.inner.borrow_mut();
        let instance = u32::from_str(&resolved).ok().ok_or_else(|| {
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
        let resolved_pin = self.io_mapper.resolve_pin(pinname);

        let mut inner = self.inner.borrow_mut();
        Ok(match inner.gpio.entry(resolved_pin.clone()) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(gpio::Pin::open(
                    Rc::clone(&self.device),
                    resolved_pin,
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
            inner.spi = Some(Rc::new(spi::Spi::open(Rc::clone(&self.device))?));
        }
        Ok(Rc::clone(inner.spi.as_ref().unwrap()))
    }

    fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Annotate>>> {
        if let Some(fpga_program) = action.downcast_ref::<FpgaProgram>() {
            // Open the console UART.  We do this first so we get the receiver
            // started and the uart buffering data for us.
            let uart = self.uart("0")?;
            if fpga_program.skip() {
                log::info!("Skip loading the __skip__ bitstream.");
                return Ok(None);
            }
            let reset_pin = self.gpio_pin("RESET")?;
            if fpga_program.check_correct_version(&*uart, &*reset_pin)? {
                return Ok(None);
            }

            // Program the FPGA bitstream.
            log::info!("Programming the FPGA bitstream.");
            let usb = self.device.borrow();
            usb.spi1_enable(false)?;
            usb.fpga_program(&fpga_program.bitstream, fpga_program.progress.as_ref())?;
            Ok(None)
        } else if action.downcast_ref::<ResetSam3x>().is_some() {
            self.device.borrow().reset_sam3x()?;
            Ok(None)
        } else if action.downcast_ref::<SetPll>().is_some() {
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
        } else if action.downcast_ref::<ClearBitstream>().is_some() {
            let usb = self.device.borrow();
            usb.spi1_enable(false)?;
            usb.clear_bitstream()?;
            Ok(None)
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }

    fn jtag(&self, opts: &JtagParams) -> Result<Rc<dyn Jtag>> {
        let mut inner = self.inner.borrow_mut();
        if inner.jtag.is_none() {
            inner.jtag = Some(Rc::new(OpenOcdServer::new(opts)?));
        }
        Ok(Rc::clone(inner.jtag.as_ref().unwrap()))
    }
}

/// Command for Transport::dispatch().
pub struct SetPll {}

/// Command for Transport::dispatch(). Resets the Chip whisperer board's SAM3X chip.
pub struct ResetSam3x {}
