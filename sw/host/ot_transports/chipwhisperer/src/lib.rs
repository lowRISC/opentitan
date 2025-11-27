// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::rc::Rc;

use anyhow::{Result, ensure};
use clap::Args;
use serialport::SerialPortType;

use opentitanlib::backend::{Backend, BackendOpts, define_interface};
use opentitanlib::io::gpio::GpioPin;
use opentitanlib::io::spi::Target;
use opentitanlib::io::uart::flow::SoftwareFlowControl;
use opentitanlib::io::uart::serial::SerialPortUart;
use opentitanlib::io::uart::{Uart, UartError};
use opentitanlib::transport::{
    Capabilities, Capability, FpgaOps, ProgressIndicator, Transport, TransportError,
    TransportInterfaceType,
};
use opentitanlib::util::fs::builtin_file;
use opentitanlib::util::parse_int::ParseInt;

pub mod board;
pub mod gpio;
pub mod spi;
pub mod usb;

use board::{Board, Cw310, Cw340};

#[derive(Default)]
struct Inner {
    spi: Option<Rc<dyn Target>>,
    gpio: HashMap<String, Rc<dyn GpioPin>>,
    uart: HashMap<u32, Rc<dyn Uart>>,
}

pub struct ChipWhisperer<B: Board> {
    device: Rc<RefCell<usb::Backend<B>>>,
    uart_override: Vec<String>,
    inner: RefCell<Inner>,
}

impl<B: Board> ChipWhisperer<B> {
    pub fn new(
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
        };
        Ok(board)
    }

    fn open_uart(&self, instance: u32) -> Result<SoftwareFlowControl<SerialPortUart>> {
        if self.uart_override.is_empty() {
            let usb = self.device.borrow();
            let serial_number = usb.get_serial_number();

            let mut ports = serialport::available_ports()
                .map_err(|e| UartError::EnumerationError(e.to_string()))?;
            ports.retain(|port| {
                if let SerialPortType::UsbPort(info) = &port.port_type
                    && info.serial_number.as_deref() == Some(serial_number)
                {
                    return true;
                }
                false
            });
            // The CW board seems to have the last port connected as OpenTitan UART 0.
            // Reverse the sort order so the last port will be instance 0.
            ports.sort_by(|a, b| b.port_name.cmp(&a.port_name));

            let port = ports.get(instance as usize).ok_or_else(|| {
                TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
            })?;
            Ok(SoftwareFlowControl::new(SerialPortUart::open(
                &port.port_name,
                B::UART_BAUD,
            )?))
        } else {
            let instance = instance as usize;
            ensure!(
                instance < self.uart_override.len(),
                TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
            );
            Ok(SoftwareFlowControl::new(SerialPortUart::open(
                &self.uart_override[instance],
                B::UART_BAUD,
            )?))
        }
    }
}

impl<B: Board + 'static> Transport for ChipWhisperer<B> {
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
                .insert(Rc::new(gpio::Pin::open(
                    self.device.clone(),
                    pinname.to_string(),
                )?))
                .clone(),
            Entry::Occupied(o) => o.get().clone(),
        })
    }

    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        ensure!(
            instance == "0",
            TransportError::InvalidInstance(TransportInterfaceType::Spi, instance.to_string())
        );
        let mut inner = self.inner.borrow_mut();
        if inner.spi.is_none() {
            inner.spi = Some(Rc::new(spi::Spi::open(self.device.clone())?));
        }
        Ok(inner.spi.as_ref().unwrap().clone())
    }

    fn fpga_ops(&self) -> Result<&dyn FpgaOps> {
        Ok(self)
    }

    fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn erased_serde::Serialize>>> {
        if action.downcast_ref::<ResetSam3x>().is_some() {
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
        } else if action.downcast_ref::<GetSam3xFwVersion>().is_some() {
            let usb = self.device.borrow();
            Ok(Some(Box::new(usb.get_firmware_version()?)))
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }
}

impl<B: Board> FpgaOps for ChipWhisperer<B> {
    fn load_bitstream(&self, bitstream: &[u8], progress: &dyn ProgressIndicator) -> Result<()> {
        // Program the FPGA bitstream.
        log::info!("Programming the FPGA bitstream.");
        let usb = self.device.borrow();
        usb.spi1_enable(false)?;
        usb.fpga_program(bitstream, progress)?;
        Ok(())
    }

    fn clear_bitstream(&self) -> Result<()> {
        let usb = self.device.borrow();
        usb.spi1_enable(false)?;
        usb.clear_bitstream()?;
        Ok(())
    }
}
/// Command for Transport::dispatch().
pub struct SetPll {}

/// Command for Transport::dispatch(). Resets the Chip whisperer board's SAM3X chip.
pub struct ResetSam3x {}

/// Command for Transport::dispatch(). Returns the SAM3X firmware version.
pub struct GetSam3xFwVersion {}

#[derive(Debug, Args)]
pub struct ChipWhispererOpts {
    /// Comma-separated list of Chip Whisperer board UARTs for non-udev environments. List the console uart first.
    #[arg(long, alias = "cw310-uarts")]
    pub uarts: Option<String>,
}

struct ChipWhispererBackend<B>(B);

impl<B: Board + 'static> Backend for ChipWhispererBackend<B> {
    type Opts = ChipWhispererOpts;

    fn create_transport(
        args: &BackendOpts,
        cw_args: &ChipWhispererOpts,
    ) -> Result<Box<dyn Transport>> {
        let uarts = cw_args
            .uarts
            .as_ref()
            .map(|v| v.split(',').collect::<Vec<&str>>())
            .unwrap_or_default();

        Ok(Box::new(ChipWhisperer::<B>::new(
            args.usb_vid,
            args.usb_pid,
            args.usb_serial.as_deref(),
            &uarts,
        )?))
    }
}

builtin_file!("opentitan.json5", include_str!("../config/opentitan.json5"));

define_interface!(
    "cw310",
    ChipWhispererBackend<Cw310>,
    "/__builtin__/opentitan_cw310.json5"
);
builtin_file!(
    "opentitan_cw310.json5",
    include_str!("../config/opentitan_cw310.json5")
);

define_interface!(
    "cw340",
    ChipWhispererBackend<Cw340>,
    "/__builtin__/opentitan_cw340.json5"
);
builtin_file!(
    "opentitan_cw340.json5",
    include_str!("../config/opentitan_cw340.json5")
);
