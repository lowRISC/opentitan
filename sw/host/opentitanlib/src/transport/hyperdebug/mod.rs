// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, ensure, Context, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use serde_annotate::Annotate;
use serialport::TTYPort;
use std::any::Any;
use std::cell::Cell;
use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fs;
use std::io::Read;
use std::io::Write;
use std::marker::PhantomData;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::io::gpio::{GpioMonitoring, GpioPin};
use crate::io::i2c::Bus;
use crate::io::jtag::{Jtag, JtagParams};
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::chip_whisperer::board::Cw310;
use crate::transport::chip_whisperer::ChipWhisperer;
use crate::transport::common::fpga::{ClearBitstream, FpgaProgram};
use crate::transport::common::uart::{flock_serial, SerialPortExclusiveLock, SerialPortUart};
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType, UpdateFirmware,
};
use crate::util::openocd::OpenOcdServer;
use crate::util::usb::UsbBackend;

pub mod c2d2;
pub mod dfu;
pub mod gpio;
pub mod i2c;
pub mod servo_micro;
pub mod spi;
pub mod ti50;

pub use c2d2::C2d2Flavor;
pub use dfu::HyperdebugDfu;
pub use servo_micro::ServoMicroFlavor;
pub use ti50::Ti50Flavor;

/// Implementation of the Transport trait for HyperDebug based on the
/// Nucleo-L552ZE-Q.
pub struct Hyperdebug<T: Flavor> {
    spi_interface: BulkInterface,
    i2c_interface: Option<BulkInterface>,
    cmsis_interface: Option<BulkInterface>,
    uart_ttys: HashMap<String, PathBuf>,
    inner: Rc<Inner>,
    current_firmware_version: Option<String>,
    phantom: PhantomData<T>,
}

/// Trait allowing slightly different treatment of USB devices that work almost like a
/// HyperDebug.  E.g. C2D2 and Servo micro.
pub trait Flavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>>;
    fn spi_index(_inner: &Rc<Inner>, instance: &str) -> Result<(u8, u8)> {
        bail!(TransportError::InvalidInstance(
            TransportInterfaceType::Spi,
            instance.to_string()
        ))
    }
    fn i2c_index(_inner: &Rc<Inner>, instance: &str) -> Result<u8> {
        bail!(TransportError::InvalidInstance(
            TransportInterfaceType::I2c,
            instance.to_string()
        ))
    }
    fn get_default_usb_vid() -> u16;
    fn get_default_usb_pid() -> u16;
    fn load_bitstream(_transport: &impl Transport, _fpga_program: &FpgaProgram) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }
    fn clear_bitstream(_clear: &ClearBitstream) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }
    fn perform_initial_fw_check() -> bool {
        true
    }
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
            usb_vid.unwrap_or_else(T::get_default_usb_vid),
            usb_pid.unwrap_or_else(T::get_default_usb_pid),
            usb_serial,
        )?;

        let path = PathBuf::from("/sys/bus/usb/devices");

        let mut console_tty: Option<PathBuf> = None;
        let mut spi_interface: Option<BulkInterface> = None;
        let mut i2c_interface: Option<BulkInterface> = None;
        let mut cmsis_interface: Option<BulkInterface> = None;
        let mut uart_ttys: HashMap<String, PathBuf> = HashMap::new();

        let config_desc = device.active_config_descriptor()?;
        let current_firmware_version = if let Some(idx) = config_desc.description_string_index() {
            if let Ok(current_firmware_version) = device.read_string_descriptor_ascii(idx) {
                if let Some(released_firmware_version) = dfu::official_firmware_version()? {
                    if T::perform_initial_fw_check()
                        && current_firmware_version != released_firmware_version
                    {
                        log::warn!(
                            "Current HyperDebug firmware version is {}, newest release is {}, Consider running `opentitantool transport update-firmware`",
                            current_firmware_version,
                            released_firmware_version,
                        );
                    }
                }
                Some(current_firmware_version)
            } else {
                None
            }
        } else {
            None
        };
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
                        // commands to be sent, to e.g. manipulate GPIOs.
                        console_tty = Some(Self::find_tty(&interface_path)?);
                    } else {
                        // We found an UART forwarding USB interface.
                        uart_ttys
                            .insert(interface_name.to_string(), Self::find_tty(&interface_path)?);
                    }
                    continue;
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
                    continue;
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
                    continue;
                }
                if interface_desc.class_code() == Self::USB_CLASS_VENDOR {
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
                    if interface_name.ends_with("CMSIS-DAP") {
                        // We found the I2C forwarding USB interface (this one interface allows
                        // multiplexing physical I2C ports.)
                        Self::find_endpoints_for_interface(
                            &mut cmsis_interface,
                            &interface,
                            &interface_desc,
                        )?;
                        continue;
                    }
                }
            }
        }
        let result = Hyperdebug::<T> {
            spi_interface: spi_interface.ok_or_else(|| {
                TransportError::CommunicationError("Missing SPI interface".to_string())
            })?,
            i2c_interface,
            cmsis_interface,
            uart_ttys,
            inner: Rc::new(Inner {
                console_tty: console_tty.ok_or_else(|| {
                    TransportError::CommunicationError("Missing console interface".to_string())
                })?,
                usb_device: RefCell::new(device),
                gpio: Default::default(),
                spis: Default::default(),
                selected_spi: Cell::new(0),
                i2cs: Default::default(),
                uarts: Default::default(),
                jtag: Default::default(),
            }),
            current_firmware_version,
            phantom: PhantomData,
        };
        Ok(result)
    }

    /// Locates the /dev/ttyUSBn node corresponding to a given interface in the sys directory
    /// tree, e.g. /sys/bus/usb/devices/1-4/1-4:1.0 .
    fn find_tty(path: &Path) -> Result<PathBuf> {
        for entry in fs::read_dir(path).context(format!("find TTY: read_dir({:?})", path))? {
            let entry = entry.context(format!("find TTY: entity {:?}", path))?;
            if let Ok(filename) = entry.file_name().into_string() {
                if filename.starts_with("tty") {
                    return Ok(PathBuf::from("/dev").join(entry.file_name()));
                }
            }
        }
        Err(TransportError::CommunicationError("Did not find ttyUSBn device".to_string()).into())
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
    selected_spi: Cell<u8>,
    i2cs: RefCell<HashMap<u8, Rc<dyn Bus>>>,
    uarts: RefCell<HashMap<PathBuf, Rc<dyn Uart>>>,
    jtag: RefCell<Option<Rc<dyn Jtag>>>,
}

impl Inner {
    /// Send a command to HyperDebug firmware, expecting to receive no output.  Any output will be
    /// reported through an `Err()` return.
    pub fn cmd_no_output(&self, cmd: &str) -> Result<()> {
        let mut unexpected_output: bool = false;
        self.execute_command(cmd, |line| {
            log::warn!("Unexpected HyperDebug output: {}", line);
            unexpected_output = true;
        })?;
        if unexpected_output {
            bail!(TransportError::CommunicationError(format!(
                "Unexpected output to {}",
                cmd
            )));
        }
        Ok(())
    }

    /// Send a command to HyperDebug firmware, expecting to receive a single line of output.  Any
    /// more or less output will be reported through an `Err()` return.
    pub fn cmd_one_line_output(&self, cmd: &str) -> Result<String> {
        let mut result: Option<String> = None;
        let mut unexpected_output: bool = false;
        self.execute_command(cmd, |line| {
            if unexpected_output {
                // Third or subsequent line, report it.
                log::warn!("Unexpected HyperDebug output: {}", line);
            } else if result.is_none() {
                // First line, remember it.
                result = Some(line.to_string());
            } else {
                // Second line, report the first as well as this one.
                log::warn!("Unexpected HyperDebug output: {}", result.as_ref().unwrap());
                log::warn!("Unexpected HyperDebug output: {}", line);
                unexpected_output = true;
            }
        })?;
        if unexpected_output {
            bail!(TransportError::CommunicationError(
                "Unexpected output".to_string()
            ));
        }
        match result {
            None => bail!(TransportError::CommunicationError(format!(
                "No response to command {}",
                cmd
            ))),
            Some(str) => Ok(str),
        }
    }

    /// Send a command to HyperDebug firmware, expecting to receive a single line of output.  Any
    /// more or less output will be reported through an `Err()` return.
    pub fn cmd_one_line_output_match<'a>(
        &self,
        cmd: &str,
        regex: &Regex,
        buf: &'a mut String,
    ) -> Result<regex::Captures<'a>> {
        *buf = self.cmd_one_line_output(cmd)?;
        let Some(captures) = regex.captures(buf) else {
            log::warn!("Unexpected HyperDebug output: {}", buf);
            bail!(TransportError::CommunicationError(
                "Unexpected output".to_string()
            ));
        };
        Ok(captures)
    }

    /// Send a command to HyperDebug firmware, with a callback to receive any output.
    fn execute_command(&self, cmd: &str, mut callback: impl FnMut(&str)) -> Result<()> {
        let port_name = self
            .console_tty
            .to_str()
            .ok_or(TransportError::UnicodePathError)?;
        let _lock = SerialPortExclusiveLock::lock(port_name)?;
        let mut port = TTYPort::open(
            &serialport::new(port_name, 115_200).timeout(std::time::Duration::from_millis(100)),
        )
        .context("Failed to open HyperDebug console")?;
        flock_serial(&port, port_name)?;

        // Send Ctrl-C, followed by the command, then newline.  This will discard any previous
        // partial input, before executing our command.
        port.write(format!("\x03{}\n", cmd).as_bytes())
            .context("communication error")?;

        // Now process response from HyperDebug.  First we expect to see the echo of the command
        // we just "typed". Then zero, one or more lines of useful output, which we want to pass
        // to the callback, and then a prompt characters, indicating that the output is
        // complete.
        let mut buf = [0u8; 128];
        let mut seen_echo = false;
        let mut len: usize = 0;
        loop {
            // Read more data, appending to existing buffer.
            match port.read(&mut buf[len..]) {
                Ok(rc) => {
                    len += rc;
                    // See if we have one or more lines terminated with endline, if so, process
                    // those and remove from the buffer by shifting the remaning data to the
                    // front of the buffer.
                    let mut line_start = 0;
                    for i in 0..len {
                        if buf[i] == b'\n' {
                            // Found a complete line, process it
                            let mut line_end = i;
                            while line_end > line_start && buf[line_end - 1] == 13 {
                                line_end -= 1;
                            }
                            let line = std::str::from_utf8(&buf[line_start..line_end])
                                .context("communication error")?;
                            if seen_echo {
                                callback(line);
                            } else if line.len() >= 2 && line[line.len() - 2..] == *"^C" {
                                // Expected output from our sending of control character.
                            } else if line.len() >= cmd.len()
                                && line[line.len() - cmd.len()..] == *cmd
                            {
                                // A line ending with the command we sent, assume this is echo,
                                // and that the actual command output will now follow.
                                seen_echo = true;
                            } else if !line.is_empty() {
                                // Unexpected output before or instead of the echo of our command.
                                log::info!("Unexpected output: {:?}", line)
                            }
                            line_start = i + 1;
                        }
                    }
                    // If any lines were processed, remove from the buffer.
                    if line_start > 0 {
                        buf.rotate_left(line_start);
                        len -= line_start;
                    }
                    if seen_echo && buf[0..len] == [b'>', b' '] {
                        // We have seen echo of the command we sent, and now the last we got was a
                        // command prompt, this is what we expect when the command has finished
                        // successfully.
                        return Ok(());
                    }
                }
                Err(error) => return Err(error).context("communication error"),
            }
        }
    }
}

impl<T: Flavor> Transport for Hyperdebug<T> {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(
            Capability::UART
                | Capability::UART_NONBLOCKING
                | Capability::GPIO
                | Capability::GPIO_MONITORING
                | Capability::SPI
                | Capability::SPI_DUAL
                | Capability::SPI_QUAD
                | Capability::I2C
                | Capability::JTAG,
        ))
    }

    fn apply_default_configuration(&self) -> Result<()> {
        self.inner.cmd_no_output("reinit")
    }

    // Create SPI Target instance, or return one from a cache of previously created instances.
    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        let (enable_cmd, idx) = T::spi_index(&self.inner, instance)?;
        if let Some(instance) = self.inner.spis.borrow().get(&idx) {
            return Ok(Rc::clone(instance));
        }
        let instance: Rc<dyn Target> = Rc::new(spi::HyperdebugSpiTarget::open(
            &self.inner,
            &self.spi_interface,
            enable_cmd,
            idx,
        )?);
        self.inner
            .spis
            .borrow_mut()
            .insert(idx, Rc::clone(&instance));
        Ok(instance)
    }

    // Create I2C Target instance, or return one from a cache of previously created instances.
    fn i2c(&self, instance: &str) -> Result<Rc<dyn Bus>> {
        let idx = T::i2c_index(&self.inner, instance)?;
        if let Some(instance) = self.inner.i2cs.borrow().get(&idx) {
            return Ok(Rc::clone(instance));
        }
        let instance: Rc<dyn Bus> = Rc::new(
            match (self.cmsis_interface.as_ref(), self.i2c_interface.as_ref()) {
                (Some(cmsis_interface), _) => i2c::HyperdebugI2cBus::open(
                    &self.inner,
                    cmsis_interface,
                    true, /* cmsis_encapsulation */
                    idx,
                )?,
                (None, Some(i2c_interface)) => i2c::HyperdebugI2cBus::open(
                    &self.inner,
                    i2c_interface,
                    false, /* cmsis_encapsulation */
                    idx,
                )?,
                (None, None) => bail!(TransportError::InvalidInstance(
                    TransportInterfaceType::I2c,
                    instance.to_string()
                )),
            },
        );
        self.inner
            .i2cs
            .borrow_mut()
            .insert(idx, Rc::clone(&instance));
        Ok(instance)
    }

    // Create Uart instance, or return one from a cache of previously created instances.
    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        match self.uart_ttys.get(instance) {
            Some(tty) => {
                if let Some(instance) = self.inner.uarts.borrow().get(tty) {
                    return Ok(Rc::clone(instance));
                }
                let instance: Rc<dyn Uart> = Rc::new(SerialPortUart::open(
                    tty.to_str().ok_or(TransportError::UnicodePathError)?,
                )?);
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

    // Create GpioPin instance, or return one from a cache of previously created instances.
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

    // Create GpioMonitoring instance.
    fn gpio_monitoring(&self) -> Result<Rc<dyn GpioMonitoring>> {
        // GpioMonitoring does not carry any state, so returning a new instance every time is
        // harmless (save for some memory usage).
        Ok(Rc::new(gpio::HyperdebugGpioMonitoring::open(&self.inner)?))
    }

    fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Annotate>>> {
        if let Some(update_firmware_action) = action.downcast_ref::<UpdateFirmware>() {
            dfu::update_firmware(
                &mut self.inner.usb_device.borrow_mut(),
                self.current_firmware_version.as_deref(),
                &update_firmware_action.firmware,
                update_firmware_action.progress.as_ref(),
                update_firmware_action.force,
            )
        } else if let Some(fpga_program) = action.downcast_ref::<FpgaProgram>() {
            T::load_bitstream(self, fpga_program).map(|_| None)
        } else if let Some(clear) = action.downcast_ref::<ClearBitstream>() {
            T::clear_bitstream(clear).map(|_| None)
        } else {
            Err(TransportError::UnsupportedOperation.into())
        }
    }

    fn jtag(&self, opts: &JtagParams) -> Result<Rc<dyn Jtag>> {
        let mut jtag = self.inner.jtag.borrow_mut();
        if jtag.is_none() {
            jtag.replace(Rc::new(OpenOcdServer::new(opts)?));
        }
        Ok(Rc::clone(jtag.as_ref().unwrap()))
    }
}

/// A `StandardFlavor` is a plain Hyperdebug board.
pub struct StandardFlavor;

impl Flavor for StandardFlavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(Rc::new(gpio::HyperdebugGpioPin::open(inner, pinname)?))
    }

    fn spi_index(inner: &Rc<Inner>, instance: &str) -> Result<(u8, u8)> {
        match instance.parse() {
            Err(_) => {
                // Execute a "spi info" command to look up the numeric index corresponding to the
                // given alphanumeric SPI instance name.
                let mut buf = String::new();
                let captures = inner
                    .cmd_one_line_output_match(
                        &format!("spi info {}", instance),
                        &SPI_REGEX,
                        &mut buf,
                    )
                    .map_err(|_| {
                        TransportError::InvalidInstance(
                            TransportInterfaceType::Spi,
                            instance.to_string(),
                        )
                    })?;
                Ok((
                    spi::USB_SPI_REQ_ENABLE,
                    captures.get(1).unwrap().as_str().parse().unwrap(),
                ))
            }
            Ok(n) => Ok((spi::USB_SPI_REQ_ENABLE, n)),
        }
    }

    fn i2c_index(inner: &Rc<Inner>, instance: &str) -> Result<u8> {
        match instance.parse() {
            Err(_) => {
                // Execute a "i2c info" command to look up the numeric index corresponding to the
                // given alphanumeric I2C instance name.
                let mut buf = String::new();
                let captures = inner
                    .cmd_one_line_output_match(
                        &format!("i2c info {}", instance),
                        &SPI_REGEX,
                        &mut buf,
                    )
                    .map_err(|_| {
                        TransportError::InvalidInstance(
                            TransportInterfaceType::I2c,
                            instance.to_string(),
                        )
                    })?;
                Ok(captures.get(1).unwrap().as_str().parse().unwrap())
            }
            Ok(n) => Ok(n),
        }
    }

    fn get_default_usb_vid() -> u16 {
        VID_GOOGLE
    }

    fn get_default_usb_pid() -> u16 {
        PID_HYPERDEBUG
    }
}

/// A `CW310Flavor` is a Hyperdebug attached to a Chip Whisperer board.  Furthermore,
/// both the Hyperdebug and Chip Whisperer board USB interfaces are attached to the host.
/// Hyperdebug is used for all IO with the Chip Whisperer board except for bitstream
/// programming.
pub struct CW310Flavor;

impl Flavor for CW310Flavor {
    fn gpio_pin(inner: &Rc<Inner>, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        StandardFlavor::gpio_pin(inner, pinname)
    }
    fn spi_index(inner: &Rc<Inner>, instance: &str) -> Result<(u8, u8)> {
        StandardFlavor::spi_index(inner, instance)
    }
    fn i2c_index(inner: &Rc<Inner>, instance: &str) -> Result<u8> {
        StandardFlavor::i2c_index(inner, instance)
    }
    fn get_default_usb_vid() -> u16 {
        StandardFlavor::get_default_usb_vid()
    }
    fn get_default_usb_pid() -> u16 {
        StandardFlavor::get_default_usb_pid()
    }
    fn load_bitstream(transport: &impl Transport, fpga_program: &FpgaProgram) -> Result<()> {
        if fpga_program.skip() {
            log::info!("Skip loading the __skip__ bitstream.");
            return Ok(());
        }

        // First, try to establish a connection to the native Chip Whisperer interface
        // which we will use for bitstream loading.
        let board = ChipWhisperer::<Cw310>::new(Default::default(), None, None, None, &[])?;

        // The transport does not provide name resolution for the IO interface
        // names, so: console=UART2 and RESET=CN10_29 on the Hyp+CW310.
        // Open the console UART.  We do this first so we get the receiver
        // started and the uart buffering data for us.
        let uart = transport.uart("UART2")?;
        let reset_pin = transport.gpio_pin("CN10_29")?;
        if fpga_program.check_correct_version(&*uart, &*reset_pin)? {
            return Ok(());
        }

        // Program the FPGA bitstream.
        log::info!("Programming the FPGA bitstream.");
        let usb = board.device.borrow();
        usb.spi1_enable(false)?;
        usb.fpga_program(&fpga_program.bitstream, fpga_program.progress.as_ref())?;
        Ok(())
    }
    fn clear_bitstream(_clear: &ClearBitstream) -> Result<()> {
        let board = ChipWhisperer::<Cw310>::new(Default::default(), None, None, None, &[])?;
        let usb = board.device.borrow();
        usb.spi1_enable(false)?;
        usb.clear_bitstream()?;
        Ok(())
    }
}

static SPI_REGEX: Lazy<Regex> = Lazy::new(|| Regex::new("^ +([0-9]+) ([^ ]+) ([0-9]+)").unwrap());
