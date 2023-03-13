// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Useful modules for OpenTitanTool application development.
pub mod command;
pub mod config;

use crate::io::emu::Emulator;
use crate::io::gpio::{GpioMonitoring, GpioPin, PinMode, PullMode};
use crate::io::i2c::Bus;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{
    Capability, Progress, ProxyOps, Transport, TransportError, TransportInterfaceType,
};
use anyhow::{bail, Result};
use std::time::Duration;

use indicatif::{ProgressBar, ProgressStyle};
use serde_annotate::Annotate;
use std::any::Any;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;
use std::vec::Vec;

const DEFAULT_TEMPLATE: &str = "[{elapsed_precise}] [{wide_bar}] {bytes}/{total_bytes} ({eta})";

/// Helper function to create a progress bar in the same form for each of
/// the commands which will use it.
pub fn progress_bar(total: u64) -> ProgressBar {
    let progress = ProgressBar::new(total);
    progress.set_style(ProgressStyle::default_bar().template(DEFAULT_TEMPLATE));
    progress
}

/// Helper struct for displaying progress bars for operations which may have multiple stages
/// (e.g. erasing then writing), or whose byte size may not be known until the operation is
/// underway.
pub struct StagedProgressBar {
    pub current_progress_bar: Rc<RefCell<Option<indicatif::ProgressBar>>>,
}

impl Default for StagedProgressBar {
    fn default() -> Self {
        Self::new()
    }
}

impl StagedProgressBar {
    const STAGE_TEMPLATE: &str =
        "{msg}: [{elapsed_precise}] [{wide_bar}] {bytes}/{total_bytes} ({eta})";

    pub fn new() -> Self {
        Self {
            current_progress_bar: Rc::new(RefCell::new(None)),
        }
    }

    /// Construct boxed progress function, suitable for passing to certain methods that perform
    /// I/O or otherwise may take a long time to complete.
    pub fn pfunc(&self) -> Box<dyn Fn(Progress)> {
        let func_rc = self.current_progress_bar.clone();
        Box::new(move |pos| match pos {
            // A new stage has started (possibly the first), record the number of bytes and its
            // name.
            Progress::Stage { name, total } => {
                let progress = progress_bar(total as u64);
                if !name.is_empty() {
                    progress.set_style(ProgressStyle::default_bar().template(Self::STAGE_TEMPLATE));
                }
                func_rc.borrow_mut().replace(progress.with_message(name));
            }
            // Progress has been made on the current state (possibly completed).
            Progress::Progress { pos } => {
                let bar = func_rc.as_ref().borrow();
                let bar = bar.as_ref().unwrap();
                if pos as u64 == bar.length() {
                    bar.finish();
                    return;
                }
                bar.set_position(pos as u64);
            }
        })
    }
}

#[derive(Default, Debug)]
pub struct PinConfiguration {
    /// The input/output mode of the GPIO pin.
    pub mode: Option<PinMode>,
    /// The default/initial level of the pin (true means high), has effect only in `PushPull` or
    /// `OpenDrain` modes.
    pub level: Option<bool>,
    /// Whether the pin has pullup/down resistor enabled.
    pub pull_mode: Option<PullMode>,
    /// The default/initial analog level of the pin in Volts, has effect only in `AnalogOutput`
    /// mode.
    pub volts: Option<f32>,
}

fn merge_field<T>(f1: &mut Option<T>, f2: Option<T>) -> Result<(), ()>
where
    T: PartialEq<T> + Copy,
{
    match (&*f1, f2) {
        (Some(v1), Some(v2)) if *v1 != v2 => return Err(()),
        (None, _) => *f1 = f2,
        _ => (),
    }
    Ok(())
}

impl PinConfiguration {
    /// Sometimes one configuration file specifies OpenDrain while leaving out the level, and
    /// another file specifies high level, while leaving out the mode.  This method will merge
    /// declarations from multiple files, as long as they are not conflicting (e.g. both PushPull
    /// and OpenDrain, or both high and low level.)
    fn merge(&mut self, other: &PinConfiguration) -> Result<(), ()> {
        merge_field(&mut self.mode, other.mode)?;
        merge_field(&mut self.level, other.level)?;
        merge_field(&mut self.pull_mode, other.pull_mode)?;
        merge_field(&mut self.volts, other.volts)?;
        Ok(())
    }
}

#[derive(Default, Debug)]
pub struct SpiConfiguration {
    pub bits_per_sec: Option<u32>,
}

impl SpiConfiguration {
    fn merge(&mut self, other: &SpiConfiguration) -> Result<(), ()> {
        merge_field(&mut self.bits_per_sec, other.bits_per_sec)?;
        Ok(())
    }
}

pub struct TransportWrapperBuilder {
    interface: String,
    pin_alias_map: HashMap<String, String>,
    uart_map: HashMap<String, String>,
    spi_map: HashMap<String, String>,
    i2c_map: HashMap<String, String>,
    pin_conf_list: Vec<(String, PinConfiguration)>,
    spi_conf_list: Vec<(String, SpiConfiguration)>,
    strapping_conf_map: HashMap<String, Vec<(String, PinConfiguration)>>,
}

// This is the structure to be passed to each Command implementation,
// replacing the "bare" Transport argument.  The fields other than
// transport will have been computed from a number ConfigurationFiles.
pub struct TransportWrapper {
    transport: RefCell<Box<dyn Transport>>,
    pin_map: HashMap<String, String>,
    uart_map: HashMap<String, String>,
    spi_map: HashMap<String, String>,
    i2c_map: HashMap<String, String>,
    pin_conf_map: HashMap<String, PinConfiguration>,
    spi_conf_map: HashMap<String, SpiConfiguration>,
    strapping_conf_map: HashMap<String, HashMap<String, PinConfiguration>>,
}

impl TransportWrapperBuilder {
    pub fn new(interface: String) -> Self {
        Self {
            interface,
            pin_alias_map: HashMap::new(),
            uart_map: HashMap::new(),
            spi_map: HashMap::new(),
            i2c_map: HashMap::new(),
            pin_conf_list: Vec::new(),
            spi_conf_list: Vec::new(),
            strapping_conf_map: HashMap::new(),
        }
    }

    fn record_pin_conf(
        pin_conf_list: &mut Vec<(String, PinConfiguration)>,
        pin_conf: &config::PinConfiguration,
    ) {
        if (None, None, None, None)
            == (
                pin_conf.mode,
                pin_conf.pull_mode,
                pin_conf.level,
                pin_conf.volts,
            )
        {
            return;
        }
        let mut conf_entry: PinConfiguration = PinConfiguration::default();
        if let Some(pin_mode) = pin_conf.mode {
            conf_entry.mode = Some(pin_mode);
        }
        if let Some(pull_mode) = pin_conf.pull_mode {
            conf_entry.pull_mode = Some(pull_mode);
        }
        if let Some(level) = pin_conf.level {
            conf_entry.level = Some(level);
        }
        if let Some(volts) = pin_conf.volts {
            conf_entry.volts = Some(volts);
        }
        pin_conf_list.push((pin_conf.name.to_string(), conf_entry))
    }

    fn record_spi_conf(
        spi_conf_list: &mut Vec<(String, SpiConfiguration)>,
        spi_conf: &config::SpiConfiguration,
    ) {
        if spi_conf.bits_per_sec.is_none() {
            return;
        }
        let mut conf_entry: SpiConfiguration = SpiConfiguration::default();
        if let Some(bits_per_sec) = spi_conf.bits_per_sec {
            conf_entry.bits_per_sec = Some(bits_per_sec);
        }
        spi_conf_list.push((spi_conf.name.to_string(), conf_entry))
    }

    pub fn add_configuration_file(&mut self, file: config::ConfigurationFile) -> Result<()> {
        if let Some(interface) = file.interface {
            if self.interface == "" {
                self.interface = interface;
            } else if self.interface == interface {
                // Same value for interface between in command line and configuration file (or
                // between multiple configuration files), nothing to update.
            } else {
                bail!(TransportError::InconsistentInterfaceConf(
                    self.interface.to_string(),
                    interface.to_string(),
                ))
            }
        }
        // Merge content of configuration file into pin_map and other members.
        for pin_conf in file.pins {
            if let Some(alias_of) = &pin_conf.alias_of {
                self.pin_alias_map
                    .insert(pin_conf.name.to_uppercase(), alias_of.clone());
            }
            // Record default input / open drain / push pull configuration to the pin.
            Self::record_pin_conf(&mut self.pin_conf_list, &pin_conf);
        }
        for strapping_conf in file.strappings {
            let strapping_pin_map = self
                .strapping_conf_map
                .entry(strapping_conf.name.to_uppercase())
                .or_default();
            for pin_conf in strapping_conf.pins {
                Self::record_pin_conf(strapping_pin_map, &pin_conf);
            }
        }
        for spi_conf in file.spi {
            if let Some(alias_of) = &spi_conf.alias_of {
                self.spi_map
                    .insert(spi_conf.name.to_uppercase(), alias_of.clone());
            }
            Self::record_spi_conf(&mut self.spi_conf_list, &spi_conf);
        }
        for uart_conf in file.uarts {
            if let Some(alias_of) = &uart_conf.alias_of {
                self.uart_map
                    .insert(uart_conf.name.to_uppercase(), alias_of.clone());
            }
            // TODO(#8769): Record baud / parity configration for later
            // use when opening uart.
        }
        Ok(())
    }

    fn consolidate_pin_conf_map(
        pin_alias_map: &HashMap<String, String>,
        pin_conf_list: &Vec<(String, PinConfiguration)>,
    ) -> Result<HashMap<String, PinConfiguration>> {
        let mut result_pin_conf_map: HashMap<String, PinConfiguration> = HashMap::new();
        for (name, conf) in pin_conf_list {
            result_pin_conf_map
                .entry(map_name(pin_alias_map, name))
                .or_default()
                .merge(conf)
                .map_err(|_| {
                    TransportError::InconsistentConf(TransportInterfaceType::Gpio, name.to_string())
                })?;
        }
        Ok(result_pin_conf_map)
    }

    fn consolidate_spi_conf_map(
        spi_alias_map: &HashMap<String, String>,
        spi_conf_list: &Vec<(String, SpiConfiguration)>,
    ) -> Result<HashMap<String, SpiConfiguration>> {
        let mut result_spi_conf_map: HashMap<String, SpiConfiguration> = HashMap::new();
        for (name, conf) in spi_conf_list {
            result_spi_conf_map
                .entry(map_name(spi_alias_map, name))
                .or_default()
                .merge(conf)
                .map_err(|_| {
                    TransportError::InconsistentConf(TransportInterfaceType::Spi, name.to_string())
                })?;
        }
        Ok(result_spi_conf_map)
    }

    pub fn get_interface(&self) -> &str {
        &self.interface
    }

    pub fn build(
        self,
        transport: Box<dyn crate::transport::Transport>,
    ) -> Result<TransportWrapper> {
        let pin_conf_map =
            Self::consolidate_pin_conf_map(&self.pin_alias_map, &self.pin_conf_list)?;
        let mut strapping_conf_map: HashMap<String, HashMap<String, PinConfiguration>> =
            HashMap::new();
        for (strapping_name, pin_conf_map) in self.strapping_conf_map {
            strapping_conf_map.insert(
                strapping_name,
                Self::consolidate_pin_conf_map(&self.pin_alias_map, &pin_conf_map)?,
            );
        }
        let spi_conf_map = Self::consolidate_spi_conf_map(&self.spi_map, &self.spi_conf_list)?;
        Ok(TransportWrapper {
            transport: RefCell::new(transport),
            pin_map: self.pin_alias_map,
            uart_map: self.uart_map,
            spi_map: self.spi_map,
            i2c_map: self.i2c_map,
            pin_conf_map,
            spi_conf_map,
            strapping_conf_map,
        })
    }
}

impl TransportWrapper {
    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    pub fn capabilities(&self) -> Result<crate::transport::Capabilities> {
        self.transport.borrow().capabilities()
    }

    /// Returns a SPI [`Target`] implementation.
    pub fn spi(&self, name: &str) -> Result<Rc<dyn Target>> {
        self.transport
            .borrow()
            .spi(map_name(&self.spi_map, name).as_str())
    }

    /// Returns a I2C [`Bus`] implementation.
    pub fn i2c(&self, name: &str) -> Result<Rc<dyn Bus>> {
        self.transport
            .borrow()
            .i2c(map_name(&self.i2c_map, name).as_str())
    }

    /// Returns a [`Uart`] implementation.
    pub fn uart(&self, name: &str) -> Result<Rc<dyn Uart>> {
        self.transport
            .borrow()
            .uart(map_name(&self.uart_map, name).as_str())
    }

    /// Returns a [`GpioPin`] implementation.
    pub fn gpio_pin(&self, name: &str) -> Result<Rc<dyn GpioPin>> {
        let resolved_pin_name = map_name(&self.pin_map, name);
        if resolved_pin_name == "NULL" {
            return Ok(Rc::new(NullPin::new(name)));
        }
        self.transport.borrow().gpio_pin(resolved_pin_name.as_str())
    }

    /// Convenience method, returns a number of [`GpioPin`] implementations.
    pub fn gpio_pins(&self, names: &[String]) -> Result<Vec<Rc<dyn GpioPin>>> {
        let mut result = Vec::new();
        for name in names {
            result.push(self.gpio_pin(name)?);
        }
        Ok(result)
    }

    /// Returns a [`GpioMonitoring`] implementation.
    pub fn gpio_monitoring(&self) -> Result<Rc<dyn GpioMonitoring>> {
        self.transport.borrow().gpio_monitoring()
    }

    /// Returns a [`Emulator`] implementation.
    pub fn emulator(&self) -> Result<Rc<dyn Emulator>> {
        self.transport.borrow().emulator()
    }

    /// Methods available only on Proxy implementation.
    pub fn proxy_ops(&self) -> Result<Rc<dyn ProxyOps>> {
        self.transport.borrow().proxy_ops()
    }

    /// Invoke non-standard functionality of some Transport implementations.
    pub fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Annotate>>> {
        self.transport.borrow().dispatch(action)
    }

    /// Apply given configuration to a single pins.
    fn apply_pin_configuration(&self, name: &str, conf: &PinConfiguration) -> Result<()> {
        let pin = self.gpio_pin(name)?;
        pin.set(conf.mode, conf.level, conf.pull_mode, conf.volts)
    }

    /// Apply given configuration to a all the given pins.
    fn apply_pin_configurations(&self, conf_map: &HashMap<String, PinConfiguration>) -> Result<()> {
        for (name, conf) in conf_map {
            self.apply_pin_configuration(name, conf)?
        }
        Ok(())
    }

    fn apply_spi_configurations(&self, conf_map: &HashMap<String, SpiConfiguration>) -> Result<()> {
        for (name, conf) in conf_map {
            let spi = self.spi(name)?;
            if let Some(bits_per_sec) = conf.bits_per_sec {
                spi.set_max_speed(bits_per_sec)?;
            }
        }
        Ok(())
    }

    /// Configure all pins as input/output, pullup, etc. as declared in configuration files.
    /// Also configure SPI port mode/speed, and other similar settings.
    pub fn apply_default_configuration(&self) -> Result<()> {
        self.transport.borrow().apply_default_configuration()?;
        self.apply_pin_configurations(&self.pin_conf_map)?;
        self.apply_spi_configurations(&self.spi_conf_map)?;
        Ok(())
    }

    /// Configure a specific set of pins as strong/weak pullup/pulldown as declared in
    /// configuration files under a given strapping name.
    pub fn apply_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        let mut success = false;
        if self.capabilities()?.request(Capability::PROXY).ok().is_ok() {
            // The transport happens to be connection to a remote opentitan session.  Pass
            // request to the remote server.
            if let Err(e) = self.proxy_ops()?.apply_pin_strapping(strapping_name) {
                match e.downcast_ref::<TransportError>() {
                    Some(TransportError::InvalidStrappingName(_)) => (),
                    _ => return Err(e),
                }
            } else {
                // Remote server recognized name of the strapping, based on its configuration.
                // Make a note of that, and do not report error even if local configuration does
                // not mention this trapping.
                success = true;
            }
        }
        if let Some(strapping_conf_map) = self.strapping_conf_map.get(strapping_name) {
            // Local configuration contains this strapping, make a note of that and do not report
            // error even if remote server did not recognize this strapping.
            success = true;
            self.apply_pin_configurations(strapping_conf_map)?;
        }
        if success {
            Ok(())
        } else {
            Err(TransportError::InvalidStrappingName(strapping_name.to_string()).into())
        }
    }

    /// Return the set of pins affected by the given strapping to their "default" (un-strapped)
    /// configuration, that is, to the level declared in the "pins" section of configuration
    /// files, outside of any "strappings" section.
    pub fn remove_pin_strapping(&self, strapping_name: &str) -> Result<()> {
        let mut success = false;
        if self.capabilities()?.request(Capability::PROXY).ok().is_ok() {
            // The transport happens to be connection to a remote opentitan session.  Pass
            // request to the remote server.
            if let Err(e) = self.proxy_ops()?.remove_pin_strapping(strapping_name) {
                match e.downcast_ref::<TransportError>() {
                    Some(TransportError::InvalidStrappingName(_)) => (),
                    _ => return Err(e),
                }
            } else {
                // Remote server recognized name of the strapping, based on its configuration.
                // Make a note of that, and do not report error even if local configuration does
                // not mention this trapping.
                success = true;
            }
        }
        if let Some(strapping_conf_map) = self.strapping_conf_map.get(strapping_name) {
            // Local configuration contains this strapping, make a note of that and do not report
            // error even if remote server did not recognize this strapping.
            success = true;
            for pin_name in strapping_conf_map.keys() {
                if let Some(default_pin_conf) = self.pin_conf_map.get(pin_name) {
                    self.apply_pin_configuration(pin_name, default_pin_conf)?;
                }
            }
        }
        if success {
            Ok(())
        } else {
            Err(TransportError::InvalidStrappingName(strapping_name.to_string()).into())
        }
    }

    pub fn reset_target(&self, reset_delay: Duration, clear_uart_rx: bool) -> Result<()> {
        log::info!("Asserting the reset signal");
        self.apply_pin_strapping("RESET")?;
        std::thread::sleep(reset_delay);
        if clear_uart_rx {
            log::info!("Clearing the UART RX buffer");
            self.uart("console")?.clear_rx_buffer()?;
        }
        log::info!("Deasserting the reset signal");
        self.remove_pin_strapping("RESET")?;
        std::thread::sleep(reset_delay);
        Ok(())
    }
}

/// Given an pin/uart/spi/i2c port name, if the name is a known alias, return the underlying
/// name/number, otherwise return the string as is.
fn map_name(map: &HashMap<String, String>, name: &str) -> String {
    let name = name.to_uppercase();
    match map.get(&name) {
        Some(v) => {
            if v.eq(&name) {
                name
            } else {
                map_name(map, v)
            }
        }
        None => name,
    }
}

/// Certain transports may want to declare that they do not support a particular pin and that it
/// should be ignored, even though its name is mentioned in e.g. generic strapping configurations.
/// (Absent any such declaration, it would result in an error to mention strappings of a pin that
/// is not in fact supported.)
struct NullPin {
    name: String,
    has_warned: Cell<bool>,
}

impl NullPin {
    fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            has_warned: Cell::new(false),
        }
    }

    /// Emit a warning the first this pin is accessed.
    fn warn(&self) {
        if !self.has_warned.get() {
            log::warn!("Accessed NULL pin {}", self.name);
            self.has_warned.set(true);
        }
    }
}

impl GpioPin for NullPin {
    fn read(&self) -> Result<bool> {
        self.warn();
        Ok(false)
    }

    fn write(&self, _value: bool) -> Result<()> {
        self.warn();
        Ok(())
    }

    fn set_mode(&self, _mode: PinMode) -> Result<()> {
        self.warn();
        Ok(())
    }

    fn set_pull_mode(&self, _mode: PullMode) -> Result<()> {
        self.warn();
        Ok(())
    }
}
