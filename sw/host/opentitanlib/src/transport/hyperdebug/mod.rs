// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs;
use std::io::ErrorKind;
use std::io::Read;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::io::gpio::GpioPin;
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{
    Capabilities, Capability, Result, Transport, TransportError, TransportInterfaceType,
    WrapInTransportError,
};
use crate::transport::common::uart::SerialPortUart;
use crate::util::usb::UsbBackend;
use crate::{bail, collection, ensure};

pub mod c2d2;
pub mod gpio;
pub mod i2c;
pub mod spi;

/// Implementation of the Transport trait for HyperDebug based on the
/// Nucleo-L552ZE-Q.
pub struct Hyperdebug<T: Flavor> {
    spi_names: HashMap<String, u8>,
    spi_interface: BulkInterface,
    i2c_names: HashMap<String, u8>,
    i2c_interface: BulkInterface,
    uart_ttys: HashMap<String, PathBuf>,
    inner: Rc<Inner>,
    phantom: PhantomData<T>,
}

/// Trait allowing slightly different treatment of USB devices that work almost like a
/// HyperDebug.  E.g. C2D2 and Servo micro.
pub trait Flavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>>;
    fn get_default_usb_vid() -> u16;
    fn get_default_usb_pid() -> u16;
}

pub const VID_GOOGLE: u16 = 0x18d1;
pub const PID_HYPERDEBUG: u16 = 0x520e;

/// Index of a single USB "interface", with its associated IN and OUT
/// endpoints.  Used to instantiate e.g. SPI trait.
#[derive(Copy, Clone)]
pub struct BulkInterface {
    interface: u8,
    in_endpoint: u8,
    out_endpoint: u8,
}

impl<T: Flavor> Hyperdebug<T> {
    const USB_CLASS_VENDOR: u8 = 255;
    const USB_SUBCLASS_UART: u8 = 80;
    const USB_SUBCLASS_SPI: u8 = 81;
    const USB_SUBCLASS_I2C: u8 = 82;
    const USB_PROTOCOL_UART: u8 = 1;
    const USB_PROTOCOL_SPI: u8 = 2;
    const USB_PROTOCOL_I2C: u8 = 1;

    /// Establish connection with a particular HyperDebug.
    pub fn open(
        usb_vid: Option<u16>,
        usb_pid: Option<u16>,
        usb_serial: Option<&str>,
    ) -> Result<Self> {
        let device = UsbBackend::new(
            usb_vid.unwrap_or(T::get_default_usb_vid()),
            usb_pid.unwrap_or(T::get_default_usb_pid()),
            usb_serial,
        )?;

        let path = PathBuf::from("/sys/bus/usb/devices");

        let mut console_tty: Option<PathBuf> = None;
        let mut spi_interface: Option<BulkInterface> = None;
        let mut i2c_interface: Option<BulkInterface> = None;
        let mut uart_ttys: HashMap<String, PathBuf> = HashMap::new();

        let config_desc = device.active_config_descriptor()?;
        // Iterate through each USB interface, discovering e.g. supported UARTs.
        for interface in config_desc.interfaces() {
            for interface_desc in interface.descriptors() {
                let ports = device
                    .port_numbers()?
                    .iter()
                    .map(|id| id.to_string())
                    .collect::<Vec<String>>()
                    .join(".");
                let interface_path = path
                    .join(format!("{}-{}", device.bus_number(), ports))
                    .join(format!(
                        "{}-{}:{}.{}",
                        device.bus_number(),
                        ports,
                        config_desc.number(),
                        interface.number()
                    ));
                // Check the class/subclass/protocol of this USB interface.
                if interface_desc.class_code() == Self::USB_CLASS_VENDOR
                    && interface_desc.sub_class_code() == Self::USB_SUBCLASS_UART
                    && interface_desc.protocol_code() == Self::USB_PROTOCOL_UART
                {
                    // A serial console interface, use the ascii name to determine if it is the
                    // HyperDebug Shell, or a UART forwarding interface.
                    let idx = match interface_desc.description_string_index() {
                        Some(idx) => idx,
                        None => continue,
                    };
                    let interface_name = match device.read_string_descriptor_ascii(idx) {
                        Ok(interface_name) => interface_name,
                        _ => continue,
                    };
                    if interface_name.ends_with("Shell") {
                        // We found the "main" control interface of HyperDebug, allowing textual
                        // commands to be sent, to e.g. manipoulate GPIOs.
                        console_tty = Some(Self::find_tty(&interface_path)?)
                    } else {
                        // We found an UART forwarding USB interface.
                        uart_ttys
                            .insert(interface_name.to_string(), Self::find_tty(&interface_path)?);
                    }
                }
                if interface_desc.class_code() == Self::USB_CLASS_VENDOR
                    && interface_desc.sub_class_code() == Self::USB_SUBCLASS_SPI
                    && interface_desc.protocol_code() == Self::USB_PROTOCOL_SPI
                {
                    // We found the SPI forwarding USB interface (this one interface allows
                    // multiplexing physical SPI ports.)
                    Self::find_endpoints_for_interface(
                        &mut spi_interface,
                        &interface,
                        &interface_desc,
                    )?;
                }
                if interface_desc.class_code() == Self::USB_CLASS_VENDOR
                    && interface_desc.sub_class_code() == Self::USB_SUBCLASS_I2C
                    && interface_desc.protocol_code() == Self::USB_PROTOCOL_I2C
                {
                    // We found the I2C forwarding USB interface (this one interface allows
                    // multiplexing physical I2C ports.)
                    Self::find_endpoints_for_interface(
                        &mut i2c_interface,
                        &interface,
                        &interface_desc,
                    )?;
                }
            }
        }
        // Eventually, the SPI aliases below should either go into configuration file, or come
        // from the HyperDebug firmware, declaring what it supports (as is the case with UARTs.)
        let spi_names: HashMap<String, u8> = collection! {
            "SPI2".to_string() => 0,
            "0".to_string() => 0,
        };
        let i2c_names: HashMap<String, u8> = collection! {
            "0".to_string() => 0,
        };
        let result = Hyperdebug::<T> {
            spi_names,
            spi_interface: spi_interface.ok_or(TransportError::CommunicationError(
                "Missing SPI interface".to_string(),
            ))?,
            i2c_names,
            i2c_interface: i2c_interface.ok_or(TransportError::CommunicationError(
                "Missing I2C interface".to_string(),
            ))?,
            uart_ttys,
            inner: Rc::new(Inner {
                console_tty: console_tty.ok_or(TransportError::CommunicationError(
                    "Missing console interface".to_string(),
                ))?,
                usb_device: RefCell::new(device),
                gpio: Default::default(),
                spis: Default::default(),
                i2cs: Default::default(),
                uarts: Default::default(),
            }),
            phantom: PhantomData,
        };
        Ok(result)
    }

    /// Locates the /dev/ttyUSBn node corresponding to a given interface in the sys directory
    /// tree, e.g. /sys/bus/usb/devices/1-4/1-4:1.0 .
    fn find_tty(path: &Path) -> Result<PathBuf> {
        for entry in fs::read_dir(path).wrap(|e| TransportError::ReadError(path.to_str().unwrap().to_string(), e))? {
            let entry = entry.wrap(|e| TransportError::ReadError(path.to_str().unwrap().to_string(), e))?;
            if let Ok(filename) = entry.file_name().into_string() {
                if filename.starts_with("tty") {
                    return Ok(PathBuf::from("/dev").join(entry.file_name()));
                }
            }
        }
        Err(TransportError::CommunicationError(
            "Did not find ttyUSBn device".to_string(),
        ))
    }

    fn find_endpoints_for_interface(
        interface_variable_output: &mut Option<BulkInterface>,
        interface: &rusb::Interface,
        interface_desc: &rusb::InterfaceDescriptor,
    ) -> Result<()> {
        let mut in_endpoint: Option<u8> = None;
        let mut out_endpoint: Option<u8> = None;
        for endpoint_desc in interface_desc.endpoint_descriptors() {
            if endpoint_desc.transfer_type() != rusb::TransferType::Bulk {
                continue;
            }
            match endpoint_desc.direction() {
                rusb::Direction::In => {
                    ensure!(
                        in_endpoint.is_none(),
                        TransportError::CommunicationError("Multiple IN endpoints".to_string())
                    );
                    in_endpoint.replace(endpoint_desc.address());
                }
                rusb::Direction::Out => {
                    ensure!(
                        out_endpoint.is_none(),
                        TransportError::CommunicationError("Multiple OUT endpoints".to_string())
                    );
                    out_endpoint.replace(endpoint_desc.address());
                }
            }
        }
        match (in_endpoint, out_endpoint) {
            (Some(in_endpoint), Some(out_endpoint)) => {
                ensure!(
                    interface_variable_output.is_none(),
                    TransportError::CommunicationError("Multiple identical interfaces".to_string())
                );
                interface_variable_output.replace(BulkInterface {
                    interface: interface.number(),
                    in_endpoint,
                    out_endpoint,
                });
                Ok(())
            }
            _ => bail!(TransportError::CommunicationError(
                "Missing one or more endpoints".to_string()
            )),
        }
    }
}

/// Internal state of the Hyperdebug struct, this struct is reference counted such that Gpio,
/// Spi and Uart sub-structs can all refer to this shared data, which is guaranteed to live on,
/// even if the caller lets the outer Hyperdebug struct run out of scope.
pub struct Inner {
    console_tty: PathBuf,
    usb_device: RefCell<UsbBackend>,
    gpio: RefCell<HashMap<String, Rc<dyn GpioPin>>>,
    spis: RefCell<HashMap<u8, Rc<dyn Target>>>,
    i2cs: RefCell<HashMap<u8, Rc<dyn Bus>>>,
    uarts: RefCell<HashMap<PathBuf, Rc<dyn Uart>>>,
}

impl Inner {
    /// Send a command to HyperDebug firmware, with a callback to receive any output.
    pub fn execute_command(&self, cmd: &str, mut callback: impl FnMut(&str)) -> Result<()> {
        let mut port = serialport::new(
            self.console_tty.to_str().ok_or(TransportError::UnicodePathError)?,
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
                    log::info!(
                        "Discarded {} characters: {:?}\n",
                        rc,
                        &std::str::from_utf8(&buf[0..rc])
                    );
                }
                Err(error) if error.kind() == ErrorKind::TimedOut => {
                    break;
                }
                Err(error) => return Err(error).wrap(TransportError::CommunicationError),
            }
        }
        // Send Ctrl-C, followed by the command, then newline.  This will discard any previous
        // partial input, before executing our command.
        port.write(format!("\x03{}\n", cmd).as_bytes())
            .wrap(TransportError::CommunicationError)?;

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
                            let line = std::str::from_utf8(&buf[line_start..line_end])
                                .wrap(TransportError::CommunicationError)?;
                            if seen_echo {
                                callback(line);
                            } else {
                                if line.len() >= cmd.len() && line[line.len() - cmd.len()..] == *cmd
                                {
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
                    if std::str::from_utf8(&buf[0..len])
                        .wrap(TransportError::CommunicationError)?
                        == "> "
                    {
                        // No data arrived for a while, and the last we got was a command
                        // prompt, this is what we expect when the command has finished
                        // successfully.
                        return Ok(());
                    } else {
                        // No data arrived for a while, but the last was no a command prompt,
                        // this could be the command taking a little time to produce its output,
                        // wait a longer while for additional data.  (Implemented by repeated
                        // calls, alternatively could have been done by fiddling with timeout
                        // setting of the underlying serial port object.)
                        repeated_timeouts += 1;
                        if repeated_timeouts == 10 {
                            return Err(error).wrap(TransportError::CommunicationError);
                        }
                    }
                }
                Err(error) => return Err(error).wrap(TransportError::CommunicationError),
            }
        }
    }
}

impl<T: Flavor> Transport for Hyperdebug<T> {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::UART | Capability::GPIO | Capability::SPI | Capability::I2C)
    }

    // Crate SPI Target instance, or return one from a cache of previously created instances.
    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        let &idx = self.spi_names.get(instance).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Spi, instance.to_string())
        })?;
        if let Some(instance) = self.inner.spis.borrow().get(&idx) {
            return Ok(Rc::clone(instance));
        }
        let instance: Rc<dyn Target> = Rc::new(spi::HyperdebugSpiTarget::open(
            &self.inner, &self.spi_interface, idx)?);
        self.inner
            .spis
            .borrow_mut()
            .insert(idx, Rc::clone(&instance));
        Ok(instance)
    }

    // Crate I2C Target instance, or return one from a cache of previously created instances.
    fn i2c(&self, instance: &str) -> Result<Rc<dyn Bus>> {
        let &idx = self.i2c_names.get(instance).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::I2c, instance.to_string())
        })?;
        if let Some(instance) = self.inner.i2cs.borrow().get(&idx) {
            return Ok(Rc::clone(instance));
        }
        let instance: Rc<dyn Bus> = Rc::new(i2c::HyperdebugI2cBus::open(
            &self.inner, &self.i2c_interface, idx)?);
        self.inner
            .i2cs
            .borrow_mut()
            .insert(idx, Rc::clone(&instance));
        Ok(instance)
    }

    // Crate Uart instance, or return one from a cache of previously created instances.
    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        match self.uart_ttys.get(instance) {
            Some(tty) => {
                if let Some(instance) = self.inner.uarts.borrow().get(tty) {
                    return Ok(Rc::clone(instance));
                }
                let instance: Rc<dyn Uart> = Rc::new(
                    SerialPortUart::open(tty.to_str().ok_or(TransportError::UnicodePathError)?)?,
                );
                self.inner
                    .uarts
                    .borrow_mut()
                    .insert(tty.clone(), Rc::clone(&instance));
                Ok(instance)
            }
            _ => Err(TransportError::InvalidInstance(
                TransportInterfaceType::Uart,
                instance.to_string(),
            )
            .into()),
        }
    }

    // Crate GpioPin instance, or return one from a cache of previously created instances.
    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(
            match self.inner.gpio.borrow_mut().entry(pinname.to_string()) {
                Entry::Vacant(v) => {
                    let u = v.insert(T::gpio_pin(&self.inner, pinname)?);
                    Rc::clone(u)
                }
                Entry::Occupied(o) => Rc::clone(o.get()),
            },
        )
    }
}

pub struct StandardFlavor {}

impl Flavor for StandardFlavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(Rc::new(gpio::HyperdebugGpioPin::open(inner, pinname)?))
    }
    fn get_default_usb_vid() -> u16 {
        VID_GOOGLE
    }
    fn get_default_usb_pid() -> u16 {
        PID_HYPERDEBUG
    }
}
