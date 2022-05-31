// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process;
use std::rc::Rc;
use std::time::{SystemTime, UNIX_EPOCH};

use crate::io::emu::Emulator;
use crate::io::gpio::GpioPin;
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{
    Capabilities, Capability, Transport, TransportError, TransportInterfaceType,
};

mod emu;
mod gpio;
mod i2c;
mod spi;
mod uart;

use crate::transport::ti50emulator::emu::{EmulatorProcess, Ti50SubProcess};
use crate::transport::ti50emulator::gpio::Ti50GpioPin;
use crate::transport::ti50emulator::i2c::Ti50I2cBus;
use crate::transport::ti50emulator::uart::Ti50Uart;

pub struct Ti50Emulator {
    inner: Rc<RefCell<Inner>>,
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

        let ti50 = Ti50Emulator {
            inner: Rc::new(RefCell::new(Inner {
                instance_directory: instance_directory.clone(),
                process: EmulatorProcess::init(
                    &instance_directory,
                    &executable_directory,
                    executable,
                )?,
                emulator: None,
                spi_map: HashMap::new(),
                gpio_map: HashMap::new(),
                i2c_map: HashMap::new(),
                uart_map: HashMap::new(),
            })),
        };
        ti50.configure_devices()?;
        Ok(ti50)
    }

    fn configure_devices(&self) -> Result<()> {
        let conf = self.inner.borrow().process.get_configurations()?;
        for (name, state) in conf.gpio_config.iter() {
            let gpio: Rc<dyn GpioPin> = Rc::new(Ti50GpioPin::open(self, name, state)?);
            self.inner
                .borrow_mut()
                .gpio_map
                .insert(name.clone(), Rc::clone(&gpio));
        }
        Ok(())
    }
}

impl Drop for Ti50Emulator {
    fn drop(&mut self) {
        log::info!(
            "Clenup Ti50Emulator instance directory: {}",
            self.inner.borrow().instance_directory.display()
        );
        if let Err(e) = fs::remove_dir_all(&self.inner.borrow().instance_directory) {
            log::error!("Can't remove instance directory error: {}", e)
        }
    }
}

/// Structure representing internal state of emulator
struct Inner {
    /// Path of parent directory representing `Ti50Emulator` instance.
    instance_directory: PathBuf,
    /// SubProcess instance
    process: EmulatorProcess,
    /// `Emualtor` instance
    emulator: Option<Rc<dyn Emulator>>,
    /// Mapping of SPI handles to their symbolic names.
    spi_map: HashMap<String, Rc<dyn Target>>,
    /// Mapping of GPIO pins handles to their symbolic names.
    gpio_map: HashMap<String, Rc<dyn GpioPin>>,
    /// Mapping of I2C handles to their symbolic names.
    i2c_map: HashMap<String, Rc<dyn Bus>>,
    /// Mapping of UART handles to their symbolic names.
    uart_map: HashMap<String, Rc<dyn Uart>>,
}

impl Inner {}

/// Implementation of the Transport trait backed based on TockOS HostEmulation port.
impl Transport for Ti50Emulator {
    fn capabilities(&self) -> Result<Capabilities> {
        Ok(Capabilities::new(
            Capability::UART
                | Capability::GPIO
                | Capability::SPI
                | Capability::I2C
                | Capability::EMULATOR,
        ))
    }

    // Returns one of existing SPI instance.
    fn spi(&self, instance: &str) -> Result<Rc<dyn Target>> {
        Ok(Rc::clone(
            self.inner.borrow().spi_map.get(instance).ok_or_else(|| {
                TransportError::InvalidInstance(TransportInterfaceType::Spi, instance.to_string())
            })?,
        ))
    }

    // Returns one of existing I2C instance.
    fn i2c(&self, instance: &str) -> Result<Rc<dyn Bus>> {
        Ok(Rc::clone(
            self.inner
                .borrow_mut()
                .i2c_map
                .entry(instance.to_string())
                .or_insert(Rc::new(Ti50I2cBus::open(self, instance)?)),
        ))
    }

    // Returns one of existing UART instance.
    fn uart(&self, instance: &str) -> Result<Rc<dyn Uart>> {
        Ok(Rc::clone(
            self.inner
                .borrow_mut()
                .uart_map
                .entry(instance.to_string())
                .or_insert(Rc::new(Ti50Uart::open(self, instance)?)),
        ))
    }

    // Returns one of existing GPIO pin instance.
    fn gpio_pin(&self, pinname: &str) -> Result<Rc<dyn GpioPin>> {
        Ok(Rc::clone(
            self.inner.borrow().gpio_map.get(pinname).ok_or_else(|| {
                TransportError::InvalidInstance(TransportInterfaceType::Gpio, pinname.to_string())
            })?,
        ))
    }

    // Create Emulator instance, or return one from a cache of previously created instances.
    fn emulator(&self) -> Result<Rc<dyn Emulator>> {
        match &mut self.inner.borrow_mut().emulator {
            Some(emu) => Ok(Rc::clone(emu)),
            slot => {
                *slot = Some(Rc::new(Ti50SubProcess::open(self)?));
                Ok(Rc::clone(slot.as_ref().unwrap()))
            }
        }
    }
}
