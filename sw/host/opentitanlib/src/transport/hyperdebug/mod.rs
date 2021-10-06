// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs;
use std::io::ErrorKind;
use std::io::Read;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use thiserror::Error;

use crate::io::gpio::GpioPin;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{Capabilities, Capability, Transport, TransportError};
use crate::collection;

pub mod gpio;
pub mod uart;
pub mod spi;

/// Implementation of the Transport trait for HyperDebug based on the
/// Nucleo-L552ZE-Q.
pub struct Hyperdebug {
    spi_names: HashMap<String, u8>,
    spi_interface: BulkInterface,
    uart_ttys: HashMap<String, PathBuf>,
    inner: Rc<Inner>,
}

/// Index of a single USB "interface", with its associated IN and OUT
/// endpoints.  Used to instantiate e.g. SPI trait.
#[derive(Copy, Clone)]
pub struct BulkInterface {
    interface: u8,
    in_endpoint: u8,
    out_endpoint: u8,
}

impl Hyperdebug {
    pub const VID_GOOGLE: u16 = 0x18d1;
    pub const PID_HYPERDEBUG: u16 = 0x520e;

    /// Establish connection with a particular HyperDebug.
    pub fn open(usb_vid: Option<u16>, usb_pid: Option<u16>, usb_serial: &Option<String>)
                -> Result<Self> {
        let devices = Self::scan(usb_vid, usb_pid, usb_serial)?;
        ensure!(!devices.is_empty(), Error::NoDevice);
        ensure!(devices.len() == 1, Error::MultipleDevices);
        match devices.get(0) {
            Some((device, _)) => Self::do_open(device),
            _ => unimplemented!(),
        }
    }

    fn do_open(device: &rusb::Device<rusb::GlobalContext>) -> Result<Self> {
        let path = PathBuf::from("/sys/bus/usb/devices");

        let mut console_tty: Option<PathBuf> = None;
        let mut spi_interface: Option<BulkInterface> = None;
        let mut uart_ttys: HashMap<String, PathBuf> = HashMap::new();

        let handle = device.open()?;
        let config_desc = device.active_config_descriptor()?;
        // Iterate through each USB interface, discovering e.g. supported UARTs.
        for interface in config_desc.interfaces() {
            for interface_desc in interface.descriptors() {
                let idx = match interface_desc.description_string_index() {
                    Some(idx) => idx,
                    None => { continue }
                };
                let interface_name = match handle.read_string_descriptor_ascii(idx) {
                    Ok(interface_name) => interface_name,
                    _ => { continue }
                };
                let ports = device.port_numbers()?.iter().map(
                    |id| id.to_string()).collect::<Vec<String>>().join(".");
                let interface_path = path
                    .join(format!("{}-{}", device.bus_number(), ports))
                    .join(format!("{}-{}:{}.{}",device.bus_number(), ports,
                                  config_desc.number(), interface.number()));
                // Check the ASCII name of this USB interface.
                match interface_name.as_str() {
                    "HyperDebug Shell" => {
                        // We found the "main" control interface of HyperDebug, allowing textual
                        // commands to be sent, to e.g. manipoulate GPIOs.
                        console_tty = Some(Self::find_tty(&interface_path)?)
                    }
                    name if name.starts_with("UART") => {
                        // We found an UART forwarding USB interface.
                        uart_ttys.insert(
                            name.to_string(),
                            Self::find_tty(&interface_path)?);
                    }
                    "SPI" => {
                        // We found the SPI forwarding USB interface (this one interface allows
                        // multiplexing physical SPI ports.)
                        let mut in_endpoint: Option<u8> = None;
                        let mut out_endpoint: Option<u8> = None;
                        for endpoint_desc in interface_desc.endpoint_descriptors() {
                            if endpoint_desc.transfer_type() != rusb::TransferType::Bulk {
                                continue;
                            }
                            match endpoint_desc.direction() {
                                rusb::Direction::In => {
                                    if let Some(_) = in_endpoint.replace(endpoint_desc.address()) {
                                        return Err(Error::CommunicationError
                                                   ("Multiple SPI IN endpoints").into());
                                    }
                                }
                                rusb::Direction::Out => {
                                    if let Some(_) = out_endpoint.replace(endpoint_desc.address()) {
                                        return Err(Error::CommunicationError
                                                   ("Multiple SPI OUT endpoints").into());
                                    }
                                }
                            }
                        }
                        match (in_endpoint, out_endpoint) {
                            (Some(in_endpoint), Some(out_endpoint)) => {
                                if let Some(_) = spi_interface.replace(BulkInterface {
                                    interface: interface.number(),
                                    in_endpoint,
                                    out_endpoint,
                                }) {
                                    return Err(Error::CommunicationError
                                               ("Multiple SPI interfaces").into());
                                }
                            }
                            _ => {
                                return Err(Error::CommunicationError
                                           ("Missing SPI interface").into());
                            }
                        }
                    }
                    _ => ()
                }
            }
        }
        // Eventually, the SPI aliases below should either go into configuration file, or come
        // from the HyperDebug firmware, declaring what it supports (as is the case with UARTs.)
        let spi_names: HashMap<String, u8> = collection! {
            "SPI2".to_string() => 0,
            "0".to_string() => 0,
        };
        let result = Hyperdebug {
            spi_names,
            spi_interface: spi_interface.ok_or(Error::CommunicationError("Missing SPI interface"))?,
            uart_ttys,
            inner: Rc::new(Inner {
                console_tty: console_tty.ok_or(Error::CommunicationError("Missing console interface"))?,
                usb_handle: RefCell::new(handle),
                gpio: Default::default(),
                spis: Default::default(),
                uarts: Default::default(),
            })
        };
        Ok(result)
    }

    /// Scan the USB bus for "our" devices, (shamelessly copied from
    /// cw310, may be able to share.)
    fn scan(
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: &Option<String>,
    ) -> Result<Vec<(rusb::Device<rusb::GlobalContext>, String)>> {
        let usb_vid = usb_vid.unwrap_or(Self::VID_GOOGLE);
        let usb_pid = usb_pid.unwrap_or(Self::PID_HYPERDEBUG);
        let mut devices = Vec::new();
        for device in rusb::devices()?.iter() {
            let descriptor = match device.device_descriptor() {
                Ok(desc) => desc,
                _ => {
                    log::error!(
                        "Could not read device descriptor for device at bus={} address={}",
                        device.bus_number(),
                        device.address()
                    );
                    continue;
                }
            };
            if descriptor.vendor_id() != usb_vid {
                continue;
            }
            if descriptor.product_id() != usb_pid {
                continue;
            }
            let handle = match device.open() {
                Ok(handle) => handle,
                _ => {
                    log::error!(
                        "Could not open device at bus={} address={}",
                        device.bus_number(),
                        device.address()
                    );
                    continue;
                }
            };
            let serial_number = match handle.read_serial_number_string_ascii(&descriptor) {
                Ok(sn) => sn,
                _ => {
                    log::error!(
                        "Could not read serial number from device at bus={} address={}",
                        device.bus_number(),
                        device.address()
                    );
                    continue;
                }
            };
            if let Some(sn) = usb_serial {
                if &serial_number != sn {
                    continue;
                }
            }
            devices.push((device, serial_number));
        }
        Ok(devices)
    }

    /// Locates the /dev/ttyUSBn node corresponding to a given interface in the sys directory
    /// tree, e.g. /sys/bus/usb/devices/1-4/1-4:1.0 .
    fn find_tty(path: &Path) -> Result<PathBuf> {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            if let Ok(filename) = entry.file_name().into_string() {
                if filename.starts_with("tty") {
                    return Ok(PathBuf::from("/dev").join(entry.file_name()));
                }
            }
        }
        Err(Error::CommunicationError("Did not find ttyUSBn device").into())
    }
}

/// Internal state of the Hyperdebug struct, this struct is reference counted such that Gpio,
/// Spi and Uart sub-structs can all refer to this shared data, which is guaranteed to live on,
/// even if the caller lets the outer Hyperdebug struct run out of scope.
pub struct Inner {
    console_tty: PathBuf,
    usb_handle: RefCell<rusb::DeviceHandle<rusb::GlobalContext>>,
    gpio: RefCell<HashMap<String, Rc<dyn GpioPin>>>,
    spis: RefCell<HashMap<u8, Rc<dyn Target>>>,
    uarts: RefCell<HashMap<PathBuf, Rc<dyn Uart>>>,
}

impl Inner {

    /// Send a command to HyperDebug firmware, with a callback to receive any output.
    pub fn execute_command(&self, cmd: &str, mut callback: impl FnMut(&str)) -> Result<()> {
        let mut port = serialport::new(
            self.console_tty.to_str().ok_or(Error::UnicodePathError)?,
            115_200,
        )
        .timeout(std::time::Duration::from_millis(10))
        .open()
        .expect("Failed to open port");

        // Ideally, we would invoke Linux flock() on the serial
        // device, to detect minicom or another instance of
        // opentitantool having the same serial port open.  Incoming
        // serial data could go silenly missing, in such cases.
        let mut buf = [0u8; 128];
        loop {
            match port.read(&mut buf) {
                Ok(rc) => {
                    log::info!("Discarded {} characters: {:?}\n", rc,
                               &std::str::from_utf8(&buf[0..rc]));
                }
                Err(error) if error.kind() == ErrorKind::TimedOut => {
                    break;
                }
                Err(error) => {
                    return Err(error.into())
                }
            }
        }
        // Send Ctrl-C, followed by the command, then newline.  This will discard any previous
        // partial input, before executing our command.
        port.write(format!("\x03{}\n", cmd).as_bytes())?;

        // Now process response from HyperDebug.  First we expect to see the echo of the command
        // we just "typed". Then zero, one or more lines of useful output, which we want to pass
        // to the callback, and then a prompt characters, indicating that the output is
        // complete.
        let mut seen_echo = false;
        let mut len: usize = 0;
        let mut repeated_timeouts: u8 = 0;
        loop {
            // Read more data, appending to existing buffer.
            match port.read(&mut buf[len..128]) {
                Ok(rc) => {
                    repeated_timeouts = 0;
                    len += rc;
                    // See if we have one or more lines terminated with endline, if so, process
                    // those and remove from the buffer by shifting the remaning data to the
                    // front of the buffer.
                    let mut line_start = 0;
                    for i in 0..len {
                        if buf[i] == b'\n' {
                            // Found a complete line, process it
                            let mut line_end = i;
                            if line_end > line_start && buf[line_end - 1] == 13 {
                                line_end -= 1;
                            }
                            let line = std::str::from_utf8(&buf[line_start..line_end])?;
                            if seen_echo {
                                callback(line);
                            } else {
                                if line.len() >= cmd.len()
                                    && line[line.len() - cmd.len()..] == *cmd {
                                    seen_echo = true;
                                }
                            }
                            line_start = i + 1;
                        }
                    }
                    // If any lines were processed, remove from the buffer.
                    if line_start > 0 {
                        buf.rotate_left(line_start);
                        len -= line_start;
                    }
                }
                Err(error) if error.kind() == ErrorKind::TimedOut => {
                    if std::str::from_utf8(&buf[0..len])? == "> " {
                        // No data arrived for a while, and the last we got was a command
                        // prompt, this is what we expect when the command has finished
                        // successfully.
                        return Ok(())
                    } else {
                        // No data arrived for a while, but the last was no a command prompt,
                        // this could be the command taking a little time to produce its output,
                        // wait a longer while for additional data.  (Implemented by repeated
                        // calls, alternatively could have been done by fiddling with timeout
                        // setting of the underlying serial port object.)
                        repeated_timeouts += 1;
                        if repeated_timeouts == 10 {
                            return Err(error.into());
                        }
                    }
                }
                Err(error) => {
                    return Err(error.into())
                }
            }
        }
    }
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("USB device did not match")]
    NoMatch,
    #[error("Found no HyperDebug USB device")]
    NoDevice,
    #[error("Found multiple HyperDebug USB devices, use --serial")]
    MultipleDevices,
    #[error("Error communicating with HyperDebug: {0}")]
    CommunicationError(&'static str),
    #[error("Encountered non-unicode path")]
    UnicodePathError,
}

impl Transport for Hyperdebug {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::UART | Capability::GPIO | Capability::SPI)
    }

    // Crate SPI Target instance, or return one from a cache of previously created instances.
    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        let &idx = self.spi_names.get(instance)
            .ok_or_else(|| TransportError::InvalidInstance("spi", instance.to_string()))?;
        if let Some(instance) = self.inner.spis.borrow().get(&idx) {
            return Ok(Rc::clone(instance));
        }
        let instance: Rc<dyn Target> = Rc::new(spi::HyperdebugSpiTarget::open(
            &self,
            idx,
        )?);
        self.inner.spis.borrow_mut().insert(idx, Rc::clone(&instance));
        Ok(instance)
    }
    
    // Crate Uart instance, or return one from a cache of previously created instances.
    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        match self.uart_ttys.get(instance) {
            Some(tty) => {
                if let Some(instance) = self.inner.uarts.borrow().get(tty) {
                    return Ok(Rc::clone(instance));
                }
                let instance: Rc<dyn Uart> = Rc::new(uart::HyperdebugUart::open(
                            &self,
                            tty,
                        )?);
                self.inner.uarts.borrow_mut().insert(tty.clone(), Rc::clone(&instance));
                Ok(instance)
            }
            _ => Err(TransportError::InvalidInstance("uart", instance.to_string()).into())
        }
    }
    
    // Crate GpioPin instance, or return one from a cache of previously created instances.
    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(match self.inner.gpio.borrow_mut().entry(pinname.to_string()) {
            Entry::Vacant(v) => {
                let u = v.insert(Rc::new(gpio::HyperdebugGpioPin::open(
                    &self,
                    pinname,
                )?));
                Rc::clone(u)
            }
            Entry::Occupied(o) => Rc::clone(o.get()),
        })
    }
}
