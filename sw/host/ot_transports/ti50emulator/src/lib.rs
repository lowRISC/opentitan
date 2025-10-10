// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::{Rc, Weak};
use std::str::FromStr;
use std::time::{SystemTime, UNIX_EPOCH};
use std::vec::Vec;

use anyhow::{Context, Result};
use clap::Args;

use opentitanlib::backend::{Backend, BackendOpts, define_interface};
use opentitanlib::io::emu::Emulator;
use opentitanlib::io::gpio::GpioPin;
use opentitanlib::io::i2c::Bus;
use opentitanlib::io::spi::Target;
use opentitanlib::io::uart::Uart;
use opentitanlib::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};
use opentitanlib::util::fs::builtin_file;

mod emu;
mod gpio;
mod i2c;
mod uart;

use crate::emu::{EmulatorImpl, EmulatorProcess, ResetPin};
use crate::gpio::Ti50GpioPin;
use crate::i2c::Ti50I2cBus;
use crate::uart::Ti50Uart;

pub struct Ti50Emulator {
    /// Mapping of GPIO pins handles to their symbolic names.
    gpio_map: HashMap<String, Rc<dyn GpioPin>>,
    /// Mapping of I2C handles to their symbolic names.
    i2c_map: HashMap<String, Rc<dyn Bus>>,
    /// Mapping of UART handles to their symbolic names.
    uart_map: HashMap<String, Rc<dyn Uart>>,
    /// Struct implementing the Emulator trait
    emu: Rc<EmulatorImpl>,
}

impl Ti50Emulator {
    /// Create new instance of [`Ti50Emulator`] based on provided parameters.
    pub fn open(
        executable_directory: &Path,
        executable: &str,
        instance_prefix: &str,
    ) -> anyhow::Result<Self> {
        let tstamp = SystemTime::now().duration_since(UNIX_EPOCH)?;
        let instance_name = format!(
            "{}_{}_{}_{}",
            instance_prefix,
            process::id(),
            tstamp.as_secs(),
            tstamp.as_nanos()
        );

        let mut instance_directory = PathBuf::from("/tmp");
        instance_directory.push(&instance_name);

        log::info!("Initializing Ti50Emulator instance: {}", instance_name);
        fs::create_dir(&instance_directory).context("Falied to create instance directory")?;

        let process = EmulatorProcess::init(&instance_directory, executable_directory, executable)?;

        let conf = process.get_configurations()?;

        let inner = Rc::new(Inner {
            instance_directory,
            process: RefCell::new(process),
            gpio_map: RefCell::default(),
            uarts: RefCell::default(),
        });

        let mut gpio_map: HashMap<String, Rc<dyn GpioPin>> = HashMap::new();
        let mut i2c_map = HashMap::new();
        let mut uart_map = HashMap::new();

        let reset_pin = ResetPin::open(&inner)?;
        gpio_map.insert("RESET".to_string(), Rc::new(reset_pin));
        for (name, state) in conf.gpio.iter() {
            inner
                .gpio_map
                .borrow_mut()
                .insert(name.to_string(), gpio::GpioConfiguration::default());
            let gpio: Rc<dyn GpioPin> = Rc::new(Ti50GpioPin::open(&inner, name, *state)?);
            gpio_map.insert(name.to_uppercase(), Rc::clone(&gpio));
        }
        for (name, path) in conf.uart.iter() {
            let uart: Rc<Ti50Uart> = Rc::new(Ti50Uart::open(&inner, path)?);
            uart_map.insert(name.to_uppercase(), Rc::clone(&uart) as Rc<dyn Uart>);
            inner.uarts.borrow_mut().push(Rc::downgrade(&uart));
        }
        for (name, path) in conf.i2c.iter() {
            let i2c: Rc<dyn Bus> = Rc::new(Ti50I2cBus::open(&inner, path)?);
            i2c_map.insert(name.to_uppercase(), Rc::clone(&i2c));
        }
        let ti50_emu = Ti50Emulator {
            gpio_map,
            i2c_map,
            uart_map,
            emu: Rc::new(EmulatorImpl::open(&inner)?),
        };
        Ok(ti50_emu)
    }
}

impl Drop for Inner {
    fn drop(&mut self) {
        log::info!(
            "Clenup Ti50Emulator instance directory: {}",
            self.instance_directory.display()
        );
        if let Err(e) = fs::remove_dir_all(&self.instance_directory) {
            log::error!("Can't remove instance directory error: {}", e)
        }
    }
}

/// Structure representing internal state of emulator
pub struct Inner {
    /// Path of parent directory representing `Ti50Emulator` instance.
    instance_directory: PathBuf,
    /// SubProcess instance
    process: RefCell<EmulatorProcess>,
    /// Current state of host drive of all GPIOs
    gpio_map: RefCell<HashMap<String, gpio::GpioConfiguration>>,
    uarts: RefCell<Vec<Weak<Ti50Uart>>>,
}

impl Inner {}

/// Implementation of the Transport trait backed based on TockOS HostEmulation port.
impl Transport for Ti50Emulator {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(
            Capability::UART | Capability::GPIO | Capability::I2C | Capability::EMULATOR,
        ))
    }

    // Returns one of existing SPI instance.
    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        Err(TransportError::InvalidInstance(
            TransportInterfaceType::Spi,
            instance.to_string(),
        ))?
    }

    // Returns one of existing I2C instance.
    fn i2c(&self, instance: &str) -> Result<Rc<dyn Bus>> {
        Ok(Rc::clone(self.i2c_map.get(instance).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::I2c, instance.to_string())
        })?))
    }

    // Returns one of existing UART instance.
    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        Ok(Rc::clone(self.uart_map.get(instance).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Uart, instance.to_string())
        })?))
    }

    // Returns one of existing GPIO pin instance.
    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(Rc::clone(self.gpio_map.get(pinname).ok_or_else(|| {
            TransportError::InvalidInstance(TransportInterfaceType::Gpio, pinname.to_string())
        })?))
    }

    // Create Emulator instance, or return one from a cache of previously created instances.
    fn emulator(&self) -> Result<Rc<dyn Emulator>> {
        Ok(self.emu.clone())
    }
}

#[derive(Debug, Args)]
pub struct Ti50EmulatorOpts {
    #[arg(long, default_value = "ti50")]
    instance_prefix: String,

    #[arg(long, value_parser = PathBuf::from_str, default_value = "")]
    executable_directory: PathBuf,

    #[arg(long, default_value = "")]
    executable: String,
}

struct Ti50EmulatorBackend;

impl Backend for Ti50EmulatorBackend {
    type Opts = Ti50EmulatorOpts;

    fn create_transport(_: &BackendOpts, args: &Ti50EmulatorOpts) -> Result<Box<dyn Transport>> {
        Ok(Box::new(Ti50Emulator::open(
            &args.executable_directory,
            &args.executable,
            &args.instance_prefix,
        )?))
    }
}

builtin_file!(
    "ti50emulator.json5",
    include_str!("../config/ti50emulator.json5")
);
define_interface!(
    "ti50emulator",
    Ti50EmulatorBackend,
    "/__builtin__/ti50emulator.json5"
);
