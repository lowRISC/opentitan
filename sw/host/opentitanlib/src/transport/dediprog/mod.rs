// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#![allow(dead_code)]
#![allow(unused_imports)]

use anyhow::{bail, ensure, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use serde_annotate::Annotate;
use serialport::SerialPortType;
use std::any::Any;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;

use crate::io::gpio::{GpioError, GpioPin, PinMode, PullMode};
use crate::io::spi::Target;
use crate::io::uart::{Uart, UartError};
use crate::transport::common::fpga::{ClearBitstream, FpgaProgram};
use crate::transport::common::uart::SerialPortUart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
use crate::util::parse_int::ParseInt;
use crate::util::usb::UsbBackend;

pub mod gpio;
pub mod spi;

pub struct Inner {
    device: UsbBackend,
    spi: Option<Rc<dyn Target>>,
    gpio: HashMap<String, Rc<dyn GpioPin>>,
    gpio_levels: u16,
    spi_clock: ClockSpeed,
    voltage: Voltage,
    in_endpoint: u8,
    out_endpoint: u8,
}

impl Inner {
    fn new(device: UsbBackend, in_endpoint: u8, out_endpoint: u8) -> Self {
        Self {
            device,
            spi: None,
            gpio: HashMap::new(),
            gpio_levels: 0xFFFF, // Low level turns on LEDs.
            spi_clock: ClockSpeed::Clk375Khz,
            voltage: Voltage::V0,
            in_endpoint,
            out_endpoint,
        }
    }

    fn set_gpio_levels(&self) -> Result<()> {
        self.device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::SetIoLed as u8,
            self.gpio_levels,
            0,
            &[],
        )?;
        Ok(())
    }

    fn set_voltage(&self) -> Result<()> {
        self.device.write_control(
            rusb::request_type(
                rusb::Direction::Out,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::SetVcc as u8,
            self.voltage as u16,
            0,
            &[],
        )?;
        Ok(())
    }
}

pub struct Dediprog {
    inner: Rc<RefCell<Inner>>,
}

#[derive(Copy, Clone)]
enum Command {
    Transceive = 0x01,
    SetIoLed = 0x07,
    ReadProgInfo = 0x08,
    SetVcc = 0x09,
    SetVoltage = 0x0B,
    Read = 0x20,
    Write = 0x30,
    SetSpiClk = 0x61,
}

#[derive(Copy, Clone)]
enum ClockSpeed {
    Clk24Mhz = 0,
    Clk12Mhz = 2,
    Clk8Mhz = 1,
    Clk3Mhz = 3,
    Clk2p18Mhz = 4,
    Clk1p5Mhz = 5,
    Clk750Khz = 6,
    Clk375Khz = 7,
}

#[derive(Copy, Clone)]
enum Voltage {
    V0 = 0x00,
    V1p8 = 0x12,
    V2p5 = 0x11,
    V3p5 = 0x10,
}

impl Dediprog {
    const VID_ST_MICROELECTRONICS: u16 = 0x0483;
    const PID_DEDIPROG_SF100: u16 = 0xDADA;

    pub fn new(
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: Option<&str>,
    ) -> anyhow::Result<Self> {
        let mut device = UsbBackend::new(
            usb_vid.unwrap_or(Self::VID_ST_MICROELECTRONICS),
            usb_pid.unwrap_or(Self::PID_DEDIPROG_SF100),
            usb_serial,
        )?;

        device.set_active_configuration(1)?;

        let config_desc = device.active_config_descriptor()?;
        // Iterate through each USB interface, discovering endpoints.
        let mut in_endpoint: Option<u8> = None;
        let mut out_endpoint: Option<u8> = None;
        for interface in config_desc.interfaces() {
            for interface_desc in interface.descriptors() {
                for endpoint_desc in interface_desc.endpoint_descriptors() {
                    if endpoint_desc.transfer_type() != rusb::TransferType::Bulk {
                        continue;
                    }
                    match endpoint_desc.direction() {
                        rusb::Direction::In => {
                            ensure!(
                                in_endpoint.is_none(),
                                TransportError::CommunicationError(
                                    "Multiple IN endpoints".to_string()
                                )
                            );
                            in_endpoint.replace(endpoint_desc.address());
                        }
                        rusb::Direction::Out => {
                            ensure!(
                                out_endpoint.is_none(),
                                TransportError::CommunicationError(
                                    "Multiple OUT endpoints".to_string()
                                )
                            );
                            out_endpoint.replace(endpoint_desc.address());
                        }
                    }
                }
            }
        }
        let (Some(in_endpoint), Some(out_endpoint)) = (in_endpoint, out_endpoint) else {
            return Err(TransportError::UsbOpenError(
                "Dediprog did not respond correctly".to_string(),
            )
            .into());
        };

        device.claim_interface(0)?;

        let protocol_version = match Self::get_protocol_version(&device) {
            Ok(protocol_version) => protocol_version,
            Err(_) => {
                let mut init_byte = [0u8];

                device.read_control(
                    rusb::request_type(
                        rusb::Direction::In,
                        rusb::RequestType::Vendor,
                        rusb::Recipient::Other,
                    ),
                    Command::SetVoltage as u8,
                    0,
                    0,
                    &mut init_byte,
                )?;

                if init_byte[0] != 0x6F {
                    return Err(TransportError::UsbOpenError(
                        "Dediprog did not respond correctly".to_string(),
                    )
                    .into());
                }
                Self::get_protocol_version(&device)?
            }
        };
        if protocol_version < 2 {
            return Err(TransportError::UsbOpenError(format!(
                "Unsupportred Dediprog protocol version: {}",
                protocol_version
            ))
            .into());
        }

        let inner = Inner::new(device, in_endpoint, out_endpoint);
        inner.set_gpio_levels()?;
        inner.set_voltage()?;
        let board = Self {
            inner: Rc::new(RefCell::new(inner)),
        };
        Ok(board)
    }

    fn get_protocol_version(device: &UsbBackend) -> Result<u32> {
        let mut device_id_bytes = [0u8; 16];
        device.read_control(
            rusb::request_type(
                rusb::Direction::In,
                rusb::RequestType::Vendor,
                rusb::Recipient::Endpoint,
            ),
            Command::ReadProgInfo as u8,
            0,
            0,
            &mut device_id_bytes,
        )?;
        let device_id_str = std::str::from_utf8(&device_id_bytes)?;
        let Some(captures) = DEDIPROG_VERSION_REGEX.captures(device_id_str) else {
            return Err(TransportError::UsbOpenError(
                format!("Unrecognized Dediprog version: {}", &device_id_str),
            )
            .into());
        };
        let product = captures.get(1).unwrap().as_str();
        let version: [u32; 3] = [
            captures.get(2).unwrap().as_str().parse()?,
            captures.get(3).unwrap().as_str().parse()?,
            captures.get(4).unwrap().as_str().parse()?,
        ];

        let protocol_version = if product == "SF100" || product == "SF200" {
            if version < [5, 5, 0] {
                1
            } else {
                2
            }
        } else if product == "SF600" {
            if version < [6, 9, 0] {
                1
            } else if version < [7, 2, 21] {
                2
            } else {
                3
            }
        } else {
            return Err(TransportError::UsbOpenError(format!(
                "Unrecognized Dediprog version: {}",
                &device_id_str
            ))
            .into());
        };
        log::info!(
            "DediProg: {}, version: {}.{}.{}, protocol V{}",
            product,
            version[0],
            version[1],
            version[2],
            protocol_version
        );
        Ok(protocol_version)
    }
}

impl Transport for Dediprog {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(Capability::SPI | Capability::GPIO))
    }

    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        if pinname == "VCC" {
            return Ok(Rc::new(VoltagePin::open(&self.inner)?));
        }
        let mut inner = self.inner.borrow_mut();
        Ok(match inner.gpio.entry(pinname.to_string()) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(gpio::DediprogPin::open(
                    Rc::clone(&self.inner),
                    pinname,
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
        if self.inner.borrow().spi.is_none() {
            self.inner.borrow_mut().spi =
                Some(Rc::new(spi::DediprogSpi::open(Rc::clone(&self.inner))?));
        }
        Ok(Rc::clone(self.inner.borrow().spi.as_ref().unwrap()))
    }
}

/// The setting of Dediprog programming voltage is exposed as a "pin" in DAC mode.
pub struct VoltagePin {
    inner: Rc<RefCell<Inner>>,
}

impl VoltagePin {
    pub fn open(inner: &Rc<RefCell<Inner>>) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(inner),
        })
    }
}

impl GpioPin for VoltagePin {
    fn read(&self) -> Result<bool> {
        bail!(TransportError::UnsupportedOperation)
    }

    /// Sets the value of the GPIO reset pin by means of the special h1_reset command.
    fn write(&self, _value: bool) -> Result<()> {
        bail!(TransportError::UnsupportedOperation)
    }

    /// Sets the mode of the GPIO pin as input, output, or open drain I/O.
    fn set_mode(&self, mode: PinMode) -> Result<()> {
        match mode {
            PinMode::AnalogOutput => Ok(()),
            _ => bail!(GpioError::UnsupportedPinMode(mode)),
        }
    }

    /// Sets the weak pull resistors of the GPIO pin.
    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        match mode {
            PullMode::None => Ok(()),
            _ => bail!(GpioError::UnsupportedPullMode(mode)),
        }
    }

    /// Reads the Dediprog voltage in Volts.
    fn analog_read(&self) -> Result<f32> {
        Ok(match self.inner.borrow().voltage {
            Voltage::V0 => 0.0,
            Voltage::V1p8 => 1.8,
            Voltage::V2p5 => 2.5,
            Voltage::V3p5 => 3.5,
        })
    }

    /// Sets the Dediprog voltage to `value` Volts.
    fn analog_write(&self, volts: f32) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        inner.voltage = if volts <= 0.3 {
            Voltage::V0
        } else if (1.6..=2.0).contains(&volts) {
            Voltage::V1p8
        } else if (2.3..=2.7).contains(&volts) {
            Voltage::V2p5
        } else if (3.0..=3.6).contains(&volts) {
            Voltage::V3p5
        } else {
            bail!(GpioError::UnsupportedPinVoltage(volts))
        };
        inner.set_voltage()
    }
}

static DEDIPROG_VERSION_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new("^([^ ]+) +V:([0-9]+)\\.([0-9]+)\\.([0-9]+)").unwrap());
