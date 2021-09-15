// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;

use std::cell::RefCell;
use std::fs;
use std::rc::Rc;

use thiserror::Error;

use crate::io::gpio::Gpio;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{Capabilities, Capability, Transport};

pub mod gpio;
pub mod uart;

pub struct Hyperdebug {
    pub path: std::path::PathBuf,
    gpio_names: Vec<String>,
    console_tty: Box<std::path::Path>,
    uart_ttys: [Box<std::path::Path>; 3],
    inner: RefCell<Inner>,
}

#[derive(Default)]
struct Inner {
    gpio: Option<Rc<dyn Gpio>>,
    _spis: [Option<Rc<dyn Target>>; 1],
    uarts: [Option<Rc<dyn Uart>>; 3],
}

impl Hyperdebug {
    pub const VID_GOOGLE: u16 = 0x18d1;
    pub const PID_HYPERDEBUG: u16 = 0x520e;

    /// Create a new `Hyperdebug` struct, optionally specifying the USB vid/pid/serial number.
    pub fn open(usb_vid: Option<u16>, usb_pid: Option<u16>, _usb_serial: &Option<String>)
                -> Result<Self> {
        let mut result: Option<Self> = Option::None;
        for entry in fs::read_dir("/sys/bus/usb/devices")? {
            let dir_entry = entry?;
            let inspect_usb_device = || -> Result<Self> {
                let vendor = u16::from_str_radix(&Self::read_string(
                    dir_entry.path().join("idVendor"))?, 16)?;
                let product = u16::from_str_radix(&Self::read_string(
                    dir_entry.path().join("idProduct"))?, 16)?;
                if vendor == usb_vid.unwrap_or(Self::VID_GOOGLE)
                    && product == usb_pid.unwrap_or(Self::PID_HYPERDEBUG) {
                        Hyperdebug::do_open(dir_entry.path())
                    } else {
                        Err(Error::NoMatch.into())
                    }
            };

            if let Ok(candidate) = inspect_usb_device() {
                match result {
                    None => {
                        result = Some(candidate);
                    }
                    Some(_) => {
                        return Err(Error::MultipleDevices.into());
                    }
                }
            }
        }
        match result {
            Some(candidate) => {
                print!("Connecting to HyperDebug device {:?}\n", candidate.path);
                Ok(candidate)
            }
            _ => Err(Error::NoDevice.into())
        }
    }

    fn do_open(path: std::path::PathBuf) -> Result<Self> {
        let mut console_tty: Option<std::path::PathBuf> = Option::None;
        let mut uart1_tty: Option<std::path::PathBuf> = Option::None;
        let mut uart2_tty: Option<std::path::PathBuf> = Option::None;
        let mut uart4_tty: Option<std::path::PathBuf> = Option::None;
        for entry in fs::read_dir(&path)? {
            let dir_entry = entry?;
            if dir_entry.file_type()?.is_dir() {
                match dir_entry.file_name().into_string() {
                    Ok(filename) => {
                        if filename.ends_with(":1.0") {
                            console_tty = Self::find_tty(&dir_entry.path())?
                        } else if filename.ends_with(":1.2") {
                            uart1_tty = Self::find_tty(&dir_entry.path())?
                        } else if filename.ends_with(":1.3") {
                            uart2_tty = Self::find_tty(&dir_entry.path())?
                        } else if filename.ends_with(":1.4") {
                            uart4_tty = Self::find_tty(&dir_entry.path())?
                        }
                    }
                    _ => ()
                }
            }
        }
        let console_tty = console_tty.ok_or(Error::NoDevice)?.into_boxed_path();
        let mut gpio_names: Vec<String> = Vec::new();
        Self::execute_command(&console_tty, &format!("gpioget"), |line| {
            gpio_names.push(line[5..].to_string());
        })?;
        let result = Hyperdebug {
            path,
            gpio_names,
            console_tty,
            uart_ttys: [
                uart1_tty.ok_or(Error::NoDevice)?.into_boxed_path(),
                uart2_tty.ok_or(Error::NoDevice)?.into_boxed_path(),
                uart4_tty.ok_or(Error::NoDevice)?.into_boxed_path()
            ],
            inner: Default::default()
        };
        Ok(result)
    }

    fn find_tty(path: &std::path::PathBuf) -> Result<Option<std::path::PathBuf>> {
        for entry in fs::read_dir(path)? {
            let dir_entry = entry?;
            match dir_entry.file_name().into_string() {
                Ok(filename) => {
                    if filename.starts_with("tty") {
                        return Ok(Option::Some(std::path::PathBuf::from("/dev")
                                               .join(dir_entry.file_name())));
                    }
                }
                _ => ()
            }
        }
        Ok(Option::None)
    }

    fn read_string(path: std::path::PathBuf) -> Result<String> {
        let file = fs::File::open(path)?;
        let mut line = String::new();
        let len = std::io::BufRead::read_line(&mut std::io::BufReader::new(file), &mut line)?;
        line.remove(len - 1);
        Ok(line)
    }

    pub fn execute_command(
        console_tty: &std::path::Path,
        cmd: &String,
        mut callback:
        impl FnMut(&String)) -> Result<()> {
        use std::io::Read;
        use std::io::Write;
        let mut port = serialport::new(console_tty.to_str().ok_or(Error::UnicodePathError)?, 115_200)
            .timeout(std::time::Duration::from_millis(100))
            .open().expect("Failed to open port");

        // Ideally, we would invoke Linux flock() on the serial
        // device, to detect minicom or another instance of
        // opentitantool having the same serial port open.  Incoming
        // serial data could go silenly missing, in such cases.
        let mut buf: [u8; 128] = [0; 128];
        loop {
            match port.read(&mut buf[0..128]) {
                Ok(rc) => {
                    print!("Discarded {} characters: {:?}\n", rc, &std::str::from_utf8(&buf[0..rc]));
                }
                Err(error) => {
                    match error.kind() {
                        std::io::ErrorKind::TimedOut => {
                            break;
                        }
                        _ => {
                            print!("Error reading: {:?}\n", error);
                            return Err(error.into())
                        }
                    }
                }
            }
        }
        port.write(format!("\u{2}{}\n", cmd).as_bytes())?;
        //std::thread::sleep(std::time::Duration::from_millis(100));
        let mut seen_echo = false;
        let mut len: usize = 0;
        loop {
            match port.read(&mut buf[len..128]) {
                Ok(rc) => {
                    len += rc;
                    'outer: loop {
                        for i in 0..len {
                            if buf[i] == 10 {
                                // Newline
                                let mut end = i;
                                if end > 0 && buf[end - 1] == 13 {
                                    end -= 1;
                                }
                                let line = std::str::from_utf8(&buf[0..end])?;
                                if seen_echo {
                                    callback(&line.to_string());
                                } else {
                                    let minmatch = std::cmp::min(6, cmd.len());
                                    if line.len() >= minmatch && line[line.len() - minmatch..]
                                        == cmd[cmd.len() - minmatch..] {
                                        seen_echo = true;
                                    }
                                }
                                buf.rotate_left(i + 1);
                                len -= i + 1;
                                continue 'outer;
                            }
                        }
                        break
                    }
                }
                Err(error) => {
                    match error.kind() {
                        std::io::ErrorKind::TimedOut => {
                            if std::str::from_utf8(&buf[0..len])? == "> " {
                                return Ok(())
                            } else {
                                print!("Timeout with {} bytes left\n", len);
                                return Ok(())
                            }
                        }
                        _ => {
                            print!("Error reading: {:?}\n", error);
                            return Err(error.into())
                        }
                    }
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
    #[error("Error communicating with HyperDebug")]
    CommunicationError,
    #[error("Encountered non-unicode path")]
    UnicodePathError,
}

impl Transport for Hyperdebug {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new(Capability::UART | Capability::GPIO | Capability::SPI)
    }

    fn uart(&self, instance: u32) -> Result<Rc<dyn Uart>> {
        let mut inner = self.inner.borrow_mut();
        if inner.uarts[instance as usize].is_none() {
            inner.uarts[instance as usize] = Some(Rc::new(uart::HyperdebugUart::open(&self, instance)?));
        }
        Ok(Rc::clone(inner.uarts[instance as usize].as_ref().unwrap()))
    }

    
    fn gpio(&self) -> Result<Rc<dyn Gpio>> {
        let mut inner = self.inner.borrow_mut();
        if inner.gpio.is_none() {
            inner.gpio = Some(Rc::new(gpio::HyperdebugGpio::open(&self)?));
        }
        Ok(Rc::clone(inner.gpio.as_ref().unwrap()))
    }
}
