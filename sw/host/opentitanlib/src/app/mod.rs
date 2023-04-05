// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Useful modules for OpenTitanTool application development.
pub mod command;
pub mod config;

use crate::io::emu::Emulator;
use crate::io::gpio::{GpioMonitoring, GpioPin, PinMode, PullMode};
use crate::io::i2c::Bus;
use crate::io::ioexpander::IoExpander;
use crate::io::jtag::{Jtag, JtagParams};
use crate::io::nonblocking_help::NonblockingHelp;
use crate::io::spi::Target;
use crate::io::uart::Uart;
use crate::transport::{
    ioexpander, Capability, ProgressIndicator, ProxyOps, Transport, TransportError,
    TransportInterfaceType,
};

use anyhow::{bail, ensure, Result};
use indicatif::{ProgressBar, ProgressStyle};
use serde_annotate::Annotate;
use std::any::Any;
use std::cell::{Cell, RefCell};
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::rc::Rc;
use std::time::Duration;
use std::vec::Vec;

pub struct NoProgressBar;

impl ProgressIndicator for NoProgressBar {
    fn new_stage(&self, _name: &str, _total: usize) {}
    fn progress(&self, _absolute: usize) {}
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
    const DEFAULT_TEMPLATE: &str = "[{elapsed_precise}] [{wide_bar}] {bytes}/{total_bytes} ({eta})";
    const STAGE_TEMPLATE: &str =
        "{msg}: [{elapsed_precise}] [{wide_bar}] {bytes}/{total_bytes} ({eta})";

    pub fn new() -> Self {
        Self {
            current_progress_bar: Rc::new(RefCell::new(None)),
        }
    }

    pub fn enable_steady_tick(&self, duration: Duration) {
        let bar = self.current_progress_bar.borrow();
        let bar = bar.as_ref().unwrap();
        bar.enable_steady_tick(duration.as_millis() as u64);
    }

    /// Returns the overall bytes per second for the most recent stage (either completed or in
    /// progress).
    pub fn bytes_per_second(&self) -> f64 {
        let bar = self.current_progress_bar.borrow();
        let bar = bar.as_ref().unwrap();
        bar.length() as f64 / bar.elapsed().as_secs_f64()
    }
}

impl ProgressIndicator for StagedProgressBar {
    fn new_stage(&self, name: &str, total: usize) {
        let progress = ProgressBar::new(total as u64);
        if name.is_empty() {
            progress.set_style(ProgressStyle::default_bar().template(Self::DEFAULT_TEMPLATE));
        } else {
            progress.set_style(ProgressStyle::default_bar().template(Self::STAGE_TEMPLATE));
        }
        self.current_progress_bar
            .borrow_mut()
            .replace(progress.with_message(name.to_string()));
    }

    fn progress(&self, pos: usize) {
        let bar = self.current_progress_bar.borrow();
        let bar = bar.as_ref().unwrap();
        if pos as u64 == bar.length() {
            bar.finish();
            return;
        }
        bar.set_position(pos as u64);
    }
}

#[derive(Clone, Copy, Default, Debug)]
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

#[derive(Default, Debug)]
pub struct I2cConfiguration {
    pub bits_per_sec: Option<u32>,
}

impl I2cConfiguration {
    fn merge(&mut self, other: &I2cConfiguration) -> Result<(), ()> {
        merge_field(&mut self.bits_per_sec, other.bits_per_sec)?;
        Ok(())
    }
}

pub struct TransportWrapperBuilder {
    interface: String,
    provides_list: Vec<(String, String)>,
    requires_list: Vec<(String, String)>,
    pin_alias_map: HashMap<String, String>,
    pin_on_io_expander_map: HashMap<String, config::IoExpanderPin>,
    uart_map: HashMap<String, String>,
    spi_map: HashMap<String, String>,
    i2c_map: HashMap<String, String>,
    pin_conf_list: Vec<(String, PinConfiguration)>,
    spi_conf_list: Vec<(String, SpiConfiguration)>,
    i2c_conf_list: Vec<(String, I2cConfiguration)>,
    strapping_conf_map: HashMap<String, Vec<(String, PinConfiguration)>>,
    io_expander_conf_map: HashMap<String, config::IoExpander>,
}

// This is the structure to be passed to each Command implementation,
// replacing the "bare" Transport argument.  The fields other than
// transport will have been computed from a number ConfigurationFiles.
pub struct TransportWrapper {
    transport: Rc<dyn Transport>,
    provides_map: HashMap<String, String>,
    pin_map: HashMap<String, String>,
    artificial_pin_map: HashMap<String, Rc<dyn GpioPin>>,
    uart_map: HashMap<String, String>,
    spi_map: HashMap<String, String>,
    i2c_map: HashMap<String, String>,
    pin_conf_map: HashMap<String, PinConfiguration>,
    spi_conf_map: HashMap<String, SpiConfiguration>,
    i2c_conf_map: HashMap<String, I2cConfiguration>,
    strapping_conf_map: HashMap<String, HashMap<String, PinConfiguration>>,
}

impl TransportWrapperBuilder {
    pub fn new(interface: String) -> Self {
        Self {
            interface,
            provides_list: Vec::new(),
            requires_list: Vec::new(),
            pin_alias_map: HashMap::new(),
            pin_on_io_expander_map: HashMap::new(),
            uart_map: HashMap::new(),
            spi_map: HashMap::new(),
            i2c_map: HashMap::new(),
            pin_conf_list: Vec::new(),
            spi_conf_list: Vec::new(),
            i2c_conf_list: Vec::new(),
            strapping_conf_map: HashMap::new(),
            io_expander_conf_map: HashMap::new(),
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

    fn record_i2c_conf(
        i2c_conf_list: &mut Vec<(String, I2cConfiguration)>,
        i2c_conf: &config::I2cConfiguration,
    ) {
        if i2c_conf.bits_per_sec.is_none() {
            return;
        }
        let mut conf_entry: I2cConfiguration = I2cConfiguration::default();
        if let Some(bits_per_sec) = i2c_conf.bits_per_sec {
            conf_entry.bits_per_sec = Some(bits_per_sec);
        }
        i2c_conf_list.push((i2c_conf.name.to_string(), conf_entry))
    }

    pub fn add_configuration_file(&mut self, file: config::ConfigurationFile) -> Result<()> {
        if let Some(interface) = file.interface {
            if self.interface.is_empty() {
                self.interface = interface;
            } else if self.interface == interface {
                // Same value for interface between in command line and configuration file (or
                // between multiple configuration files), nothing to update.
            } else {
                bail!(TransportError::InconsistentInterfaceConf(
                    self.interface.to_string(),
                    interface,
                ))
            }
        }
        for (key, value) in file.provides {
            self.provides_list.push((key, value));
        }
        for (key, value) in file.requires {
            self.requires_list.push((key, value));
        }
        // Merge content of configuration file into pin_map and other members.
        for pin_conf in file.pins {
            if let Some(alias_of) = &pin_conf.alias_of {
                self.pin_alias_map
                    .insert(pin_conf.name.to_uppercase(), alias_of.clone());
            } else if let Some(on_io_expander) = &pin_conf.on_io_expander {
                ensure!(
                    &pin_conf.alias_of.is_none(),
                    TransportError::InconsistentConf(
                        TransportInterfaceType::Gpio,
                        pin_conf.name.to_string()
                    )
                );
                let uppercase_name = pin_conf.name.to_uppercase();
                ensure!(
                    !self.pin_on_io_expander_map.contains_key(&uppercase_name),
                    TransportError::InconsistentConf(
                        TransportInterfaceType::Gpio,
                        pin_conf.name.to_string()
                    )
                );
                self.pin_on_io_expander_map
                    .insert(uppercase_name, on_io_expander.clone());
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
        for i2c_conf in file.i2c {
            if let Some(alias_of) = &i2c_conf.alias_of {
                self.i2c_map
                    .insert(i2c_conf.name.to_uppercase(), alias_of.clone());
            }
            Self::record_i2c_conf(&mut self.i2c_conf_list, &i2c_conf);
        }
        for uart_conf in file.uarts {
            if let Some(alias_of) = &uart_conf.alias_of {
                self.uart_map
                    .insert(uart_conf.name.to_uppercase(), alias_of.clone());
            }
            // TODO(#8769): Record baud / parity configration for later
            // use when opening uart.
        }
        for io_expander_conf in file.io_expanders {
            match self
                .io_expander_conf_map
                .entry(io_expander_conf.name.to_string())
            {
                Entry::Vacant(v) => {
                    v.insert(io_expander_conf);
                }
                Entry::Occupied(_) => bail!(TransportError::InconsistentConf(
                    TransportInterfaceType::IoExpander,
                    io_expander_conf.name
                )),
            }
        }
        Ok(())
    }

    fn consolidate_provides_map(
        result_provides_map: &mut HashMap<String, String>,
        provides_list: Vec<(String, String)>,
    ) -> Result<()> {
        for (key, value) in provides_list {
            match result_provides_map.entry(key.clone()) {
                Entry::Vacant(v) => {
                    v.insert(value);
                }
                Entry::Occupied(v) => {
                    if v.get() != &value {
                        bail!(TransportError::InconsistentConf(
                            TransportInterfaceType::Provides,
                            key
                        ))
                    }
                }
            }
        }
        Ok(())
    }

    fn verify_requires_list(
        provides_map: &HashMap<String, String>,
        requires_list: &Vec<(String, String)>,
    ) -> Result<()> {
        for (key, required_value) in requires_list {
            match provides_map.get(key) {
                Some(actual_value) if actual_value == required_value => (),
                Some(actual_value) => bail!(TransportError::RequiresUnequal(
                    key.to_string(),
                    required_value.to_string(),
                    actual_value.to_string()
                )),
                None => bail!(TransportError::RequiresMissing(
                    key.to_string(),
                    required_value.to_string()
                )),
            }
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

    fn consolidate_i2c_conf_map(
        i2c_alias_map: &HashMap<String, String>,
        i2c_conf_list: &Vec<(String, I2cConfiguration)>,
    ) -> Result<HashMap<String, I2cConfiguration>> {
        let mut result_i2c_conf_map: HashMap<String, I2cConfiguration> = HashMap::new();
        for (name, conf) in i2c_conf_list {
            result_i2c_conf_map
                .entry(map_name(i2c_alias_map, name))
                .or_default()
                .merge(conf)
                .map_err(|_| {
                    TransportError::InconsistentConf(TransportInterfaceType::I2c, name.to_string())
                })?;
        }
        Ok(result_i2c_conf_map)
    }

    pub fn get_interface(&self) -> &str {
        &self.interface
    }

    pub fn build(
        self,
        transport: Box<dyn crate::transport::Transport>,
    ) -> Result<TransportWrapper> {
        let mut provides_map = if transport
            .capabilities()?
            .request(Capability::PROXY)
            .ok()
            .is_ok()
        {
            transport.proxy_ops()?.provides_map()?
        } else {
            HashMap::new()
        };
        Self::consolidate_provides_map(&mut provides_map, self.provides_list)?;
        Self::verify_requires_list(&provides_map, &self.requires_list)?;

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
        let i2c_conf_map = Self::consolidate_i2c_conf_map(&self.i2c_map, &self.i2c_conf_list)?;
        let mut transport_wrapper = TransportWrapper {
            transport: Rc::from(transport),
            provides_map,
            pin_map: self.pin_alias_map,
            artificial_pin_map: HashMap::new(),
            uart_map: self.uart_map,
            spi_map: self.spi_map,
            i2c_map: self.i2c_map,
            pin_conf_map,
            spi_conf_map,
            i2c_conf_map,
            strapping_conf_map,
        };
        let mut io_expanders: HashMap<String, IoExpander> = HashMap::new();
        for (name, conf) in self.io_expander_conf_map {
            io_expanders.insert(
                name.to_string(),
                ioexpander::create(&conf, &transport_wrapper)?,
            );
        }
        transport_wrapper
            .artificial_pin_map
            .insert("NULL".to_string(), Rc::new(NullPin::new()));
        for (pinname, v) in self.pin_on_io_expander_map {
            if let Some(io) = io_expanders.get(&v.io_expander) {
                ensure!(
                    (v.pin_no as usize) < io.pins.len(),
                    TransportError::InvalidIoExpanderPinNo(v.io_expander.to_string(), v.pin_no)
                );
                transport_wrapper
                    .artificial_pin_map
                    .insert(pinname, Rc::clone(&io.pins[v.pin_no as usize]));
            } else {
                bail!(TransportError::InvalidIoExpanderName(
                    v.io_expander.to_string()
                ));
            }
        }
        Ok(transport_wrapper)
    }
}

impl TransportWrapper {
    /// Returns a `Capabilities` object to check the capabilities of this
    /// transport object.
    pub fn capabilities(&self) -> Result<crate::transport::Capabilities> {
        self.transport.capabilities()
    }

    /// Returns a string->string map containing user-defined aspects "provided" by the testbed
    /// setup.  For instance, whether a SPI flash chip is fitted in the socket, or whether pullup
    /// resistors are suitable for high-speed I2C.
    pub fn provides_map(&self) -> Result<&HashMap<String, String>> {
        Ok(&self.provides_map)
    }

    pub fn query_provides(&self, key: &str) -> Result<&str> {
        self.provides_map
            .get(key)
            .map(String::as_str)
            .ok_or_else(|| {
                TransportError::InvalidInstance(TransportInterfaceType::Provides, key.to_string())
                    .into()
            })
    }

    /// Returns a [`Jtag`] implementation.
    pub fn jtag(&self, opts: &JtagParams) -> Result<Rc<dyn Jtag>> {
        self.transport.jtag(opts)
    }

    /// Returns a SPI [`Target`] implementation.
    pub fn spi(&self, name: &str) -> Result<Rc<dyn Target>> {
        self.transport.spi(map_name(&self.spi_map, name).as_str())
    }

    /// Returns a I2C [`Bus`] implementation.
    pub fn i2c(&self, name: &str) -> Result<Rc<dyn Bus>> {
        self.transport.i2c(map_name(&self.i2c_map, name).as_str())
    }

    /// Returns a [`Uart`] implementation.
    pub fn uart(&self, name: &str) -> Result<Rc<dyn Uart>> {
        self.transport.uart(map_name(&self.uart_map, name).as_str())
    }

    /// Returns a [`GpioPin`] implementation.
    pub fn gpio_pin(&self, name: &str) -> Result<Rc<dyn GpioPin>> {
        let resolved_pin_name = map_name(&self.pin_map, name);
        if let Some(pin) = self.artificial_pin_map.get(&resolved_pin_name) {
            return Ok(pin.clone());
        }
        self.transport.gpio_pin(resolved_pin_name.as_str())
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
        self.transport.gpio_monitoring()
    }

    pub fn pin_strapping(&self, name: &str) -> Result<PinStrapping> {
        let proxy = if self.capabilities()?.request(Capability::PROXY).ok().is_ok() {
            Some(self.proxy_ops()?)
        } else {
            None
        };
        let mut pins = Vec::new();
        if let Some(strapping_conf_map) = self.strapping_conf_map.get(name) {
            for (pin_name, conf) in strapping_conf_map {
                pins.push(StrappedPin {
                    pin: self.gpio_pin(pin_name)?,
                    strapped: *conf,
                    original: self.pin_conf_map.get(pin_name).copied(),
                });
            }
        } else if proxy.is_none() {
            bail!(TransportError::InvalidStrappingName(name.to_string()));
        }
        Ok(PinStrapping {
            proxy,
            name: name.to_string(),
            pins,
        })
    }

    /// Returns a [`Emulator`] implementation.
    pub fn emulator(&self) -> Result<Rc<dyn Emulator>> {
        self.transport.emulator()
    }

    /// Methods available only on Proxy implementation.
    pub fn proxy_ops(&self) -> Result<Rc<dyn ProxyOps>> {
        self.transport.proxy_ops()
    }

    /// Invoke non-standard functionality of some Transport implementations.
    pub fn dispatch(&self, action: &dyn Any) -> Result<Option<Box<dyn Annotate>>> {
        self.transport.dispatch(action)
    }

    pub fn nonblocking_help(&self) -> Result<Rc<dyn NonblockingHelp>> {
        self.transport.nonblocking_help()
    }

    /// Apply given configuration to a single pins.
    fn apply_pin_configuration(&self, name: &str, conf: &PinConfiguration) -> Result<()> {
        let pin = self.gpio_pin(name)?;
        pin.set(conf.mode, conf.level, conf.pull_mode, conf.volts)
    }

    /// Apply given configuration to a all the given pins.
    fn apply_pin_configurations(&self, conf_map: &HashMap<String, PinConfiguration>) -> Result<()> {
        // Pins on IO expanders will rely on some "direct" pins being configured for I2C and
        // possibly MUX strappings.  To account for that, first apply the configuration to all
        // "direct" (non-artificial) pins, and then to the rest.  (In theory, an IO expander could
        // be cascaded behind other IO expanders, requiring more complicated management of a
        // dependency graph, if that ever becomes an issue, a topological sort in
        // `TransportWrapperBuilder.build()` would probably be appropriate.)
        for (name, conf) in conf_map {
            if !self.artificial_pin_map.contains_key(name) {
                self.apply_pin_configuration(name, conf)?;
            }
        }
        for (name, conf) in conf_map {
            if self.artificial_pin_map.contains_key(name) {
                self.apply_pin_configuration(name, conf)?;
            }
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

    fn apply_i2c_configurations(&self, conf_map: &HashMap<String, I2cConfiguration>) -> Result<()> {
        for (name, conf) in conf_map {
            let i2c = self.i2c(name)?;
            if let Some(bits_per_sec) = conf.bits_per_sec {
                i2c.set_max_speed(bits_per_sec)?;
            }
        }
        Ok(())
    }

    /// Configure all pins as input/output, pullup, etc. as declared in configuration files.
    /// Also configure SPI port mode/speed, and other similar settings.
    pub fn apply_default_configuration(&self) -> Result<()> {
        self.transport.apply_default_configuration()?;
        self.apply_pin_configurations(&self.pin_conf_map)?;
        self.apply_spi_configurations(&self.spi_conf_map)?;
        self.apply_i2c_configurations(&self.i2c_conf_map)?;
        Ok(())
    }

    pub fn reset_target(&self, reset_delay: Duration, clear_uart_rx: bool) -> Result<()> {
        let reset_strapping = self.pin_strapping("RESET")?;
        log::info!("Asserting the reset signal");
        reset_strapping.apply()?;
        std::thread::sleep(reset_delay);
        if clear_uart_rx {
            log::info!("Clearing the UART RX buffer");
            self.uart("console")?.clear_rx_buffer()?;
        }
        log::info!("Deasserting the reset signal");
        reset_strapping.remove()?;
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
    has_warned: Cell<bool>,
}

impl NullPin {
    fn new() -> Self {
        Self {
            has_warned: Cell::new(false),
        }
    }

    /// Emit a warning the first this pin is accessed.
    fn warn(&self) {
        if !self.has_warned.get() {
            log::warn!("Accessed NULL pin");
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

/// Represents configuration of a set of pins as strong/weak pullup/pulldown as declared in
/// configuration files under a given strapping name.
pub struct PinStrapping {
    name: String,
    proxy: Option<Rc<dyn ProxyOps>>,
    pins: Vec<StrappedPin>,
}

struct StrappedPin {
    pin: Rc<dyn GpioPin>,
    strapped: PinConfiguration,
    original: Option<PinConfiguration>,
}

impl PinStrapping {
    /// Configure the set of pins as strong/weak pullup/pulldown as declared in configuration
    /// files under a given strapping name.
    pub fn apply(&self) -> Result<()> {
        if let Some(ref proxy_ops) = self.proxy {
            // The transport happens to be connected to a remote opentitan session.  First, pass
            // the request to the remote server.
            if let Err(e) = proxy_ops.apply_pin_strapping(&self.name) {
                match e.downcast_ref::<TransportError>() {
                    Some(TransportError::InvalidStrappingName(_)) => {
                        if self.pins.is_empty() {
                            return Err(e);
                        }
                    }
                    _ => return Err(e),
                }
            }
        }
        for StrappedPin {
            pin,
            strapped: conf,
            original: _,
        } in &self.pins
        {
            pin.set(conf.mode, conf.level, conf.pull_mode, conf.volts)?
        }
        Ok(())
    }

    /// Return the set of pins affected by the given strapping to their "default" (un-strapped)
    /// configuration, that is, to the level declared in the "pins" section of configuration
    /// files, outside of any "strappings" section.
    pub fn remove(&self) -> Result<()> {
        if let Some(ref proxy_ops) = self.proxy {
            // The transport happens to be connection to a remote opentitan session.  Pass
            // request to the remote server.
            if let Err(e) = proxy_ops.remove_pin_strapping(&self.name) {
                match e.downcast_ref::<TransportError>() {
                    Some(TransportError::InvalidStrappingName(_)) => {
                        if self.pins.is_empty() {
                            return Err(e);
                        }
                    }
                    _ => return Err(e),
                }
            }
        }
        for StrappedPin {
            pin,
            strapped: _,
            original,
        } in &self.pins
        {
            if let Some(conf) = original {
                pin.set(conf.mode, conf.level, conf.pull_mode, conf.volts)?
            }
        }
        Ok(())
    }
}
