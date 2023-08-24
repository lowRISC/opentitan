// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! Useful modules for OpenTitanTool application development.
pub mod command;
pub mod config;

use crate::io;
use crate::io::eeprom;
use crate::io::emu::Emulator;
use crate::io::gpio::{GpioMonitoring, GpioPin, PinConfiguration, PinMode, PullMode};
use crate::io::i2c::{self, Bus, I2cConfiguration};
use crate::io::io_mapper::{AliasMapper, IoMapper};
use crate::io::ioexpander::IoExpander;
use crate::io::jtag::{Jtag, JtagParams};
use crate::io::nonblocking_help::NonblockingHelp;
use crate::io::spi;
use crate::io::spi::{SpiConfiguration, Target};
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
        bar.enable_steady_tick(duration);
    }

    /// Returns the overall bytes per second for the most recent stage (either completed or in
    /// progress).
    pub fn bytes_per_second(&self) -> f64 {
        let bar = self.current_progress_bar.borrow();
        let bar = bar.as_ref().unwrap();
        bar.length().unwrap() as f64 / bar.elapsed().as_secs_f64()
    }
}

impl ProgressIndicator for StagedProgressBar {
    fn new_stage(&self, name: &str, total: usize) {
        let progress = ProgressBar::new(total as u64);
        if name.is_empty() {
            progress.set_style(
                ProgressStyle::default_bar()
                    .template(Self::DEFAULT_TEMPLATE)
                    .unwrap(),
            );
        } else {
            progress.set_style(
                ProgressStyle::default_bar()
                    .template(Self::STAGE_TEMPLATE)
                    .unwrap(),
            );
        }
        self.current_progress_bar
            .borrow_mut()
            .replace(progress.with_message(name.to_string()));
    }

    fn progress(&self, pos: usize) {
        let bar = self.current_progress_bar.borrow();
        let bar = bar.as_ref().unwrap();
        if pos as u64 == bar.length().unwrap() {
            bar.finish();
            return;
        }
        bar.set_position(pos as u64);
    }
}

pub struct TransportWrapperBuilder {
    interface: String,
    provides_list: Vec<(String, String)>,
    requires_list: Vec<(String, String)>,
    pin_alias_map: AliasMapper,
    pin_on_io_expander_map: HashMap<String, config::IoExpanderPin>,
    uart_map: AliasMapper,
    i2c_map: AliasMapper,
    pin_conf_list: Vec<(String, PinConfiguration)>,
    spi_conf_map: HashMap<String, config::SpiConfiguration>,
    i2c_conf_map: HashMap<String, config::I2cConfiguration>,
    strapping_conf_map: HashMap<String, Vec<(String, PinConfiguration)>>,
    io_expander_conf_map: HashMap<String, config::IoExpander>,
}

impl TransportWrapperBuilder {
    pub fn new(interface: String) -> Self {
        Self {
            interface,
            provides_list: Vec::new(),
            requires_list: Vec::new(),
            pin_alias_map: AliasMapper::new(),
            pin_on_io_expander_map: HashMap::new(),
            uart_map: AliasMapper::new(),
            i2c_map: AliasMapper::new(),
            pin_conf_list: Vec::new(),
            spi_conf_map: HashMap::new(),
            i2c_conf_map: HashMap::new(),
            strapping_conf_map: HashMap::new(),
            io_expander_conf_map: HashMap::new(),
        }
    }

    fn record_pin_conf(
        pin_conf_list: &mut Vec<(String, PinConfiguration)>,
        pin_conf: &config::PinConfiguration,
    ) {
        if (None, None, None, None, None)
            == (
                pin_conf.mode,
                pin_conf.pull_mode,
                pin_conf.level,
                pin_conf.volts,
                pin_conf.invert,
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
        conf_entry.invert = pin_conf.invert.unwrap_or(false);
        pin_conf_list.push((pin_conf.name.to_string(), conf_entry))
    }

    fn record_spi_conf(
        spi_conf_map: &mut HashMap<String, config::SpiConfiguration>,
        spi_conf: &config::SpiConfiguration,
    ) -> Option<()> {
        let entry = spi_conf_map
            .entry(spi_conf.name.to_string())
            .or_insert_with(|| config::SpiConfiguration {
                name: spi_conf.name.clone(),
                ..Default::default()
            });
        io::merge_configuration_field(&mut entry.mode, &spi_conf.mode)?;
        io::merge_configuration_field(&mut entry.bits_per_word, &spi_conf.bits_per_word)?;
        io::merge_configuration_field(&mut entry.bits_per_sec, &spi_conf.bits_per_sec)?;
        io::merge_configuration_field(&mut entry.chip_select, &spi_conf.chip_select)?;
        io::merge_configuration_field(&mut entry.alias_of, &spi_conf.alias_of)
    }

    fn record_i2c_conf(
        i2c_conf_map: &mut HashMap<String, config::I2cConfiguration>,
        i2c_conf: &config::I2cConfiguration,
    ) -> Option<()> {
        let entry = i2c_conf_map
            .entry(i2c_conf.name.to_string())
            .or_insert_with(|| config::I2cConfiguration {
                name: i2c_conf.name.clone(),
                ..Default::default()
            });
        io::merge_configuration_field(&mut entry.address, &i2c_conf.address)?;
        io::merge_configuration_field(&mut entry.bits_per_sec, &i2c_conf.bits_per_sec)?;
        io::merge_configuration_field(&mut entry.alias_of, &i2c_conf.alias_of)
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
            Self::record_spi_conf(&mut self.spi_conf_map, &spi_conf).ok_or(
                TransportError::InconsistentConf(
                    TransportInterfaceType::Spi,
                    spi_conf.name.to_string(),
                ),
            )?;
        }
        for i2c_conf in file.i2c {
            Self::record_i2c_conf(&mut self.i2c_conf_map, &i2c_conf).ok_or(
                TransportError::InconsistentConf(
                    TransportInterfaceType::I2c,
                    i2c_conf.name.to_string(),
                ),
            )?;
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
        pin_alias_map: &AliasMapper,
        pin_conf_list: &Vec<(String, PinConfiguration)>,
    ) -> Result<HashMap<String, PinConfiguration>> {
        let mut result_pin_conf_map: HashMap<String, PinConfiguration> = HashMap::new();
        for (name, conf) in pin_conf_list {
            result_pin_conf_map
                .entry(pin_alias_map.resolve(name))
                .or_default()
                .merge(conf)
                .ok_or(TransportError::InconsistentConf(
                    TransportInterfaceType::Gpio,
                    name.to_string(),
                ))?;
        }
        Ok(result_pin_conf_map)
    }

    fn resolve_spi_conf(
        name: &str,
        spi_conf_map: &HashMap<String, config::SpiConfiguration>,
        pin_alias_map: &AliasMapper,
    ) -> SpiConfiguration {
        if let Some(entry) = spi_conf_map.get(name) {
            let mut conf = if let Some(ref alias_of) = entry.alias_of {
                Self::resolve_spi_conf(alias_of.as_str(), spi_conf_map, pin_alias_map)
            } else {
                SpiConfiguration {
                    underlying_instance: name.to_string(),
                    ..Default::default()
                }
            };
            // Apply configuration from this level
            if let Some(chip_select) = entry.chip_select.as_ref() {
                conf.chip_select = Some(pin_alias_map.resolve(chip_select));
            }
            if let Some(mode) = entry.mode {
                conf.mode = Some(mode);
            }
            if let Some(bits_per_sec) = entry.bits_per_sec {
                conf.bits_per_sec = Some(bits_per_sec);
            }
            if let Some(bits_per_word) = entry.bits_per_word {
                conf.bits_per_word = Some(bits_per_word);
            }
            conf
        } else {
            SpiConfiguration {
                underlying_instance: name.to_string(),
                ..Default::default()
            }
        }
    }

    fn consolidate_spi_conf_map(
        spi_conf_map: &HashMap<String, config::SpiConfiguration>,
        pin_alias_map: &AliasMapper,
    ) -> Result<HashMap<String, SpiConfiguration>> {
        let mut resolved_spi_conf_map = HashMap::new();
        for name in spi_conf_map.keys() {
            resolved_spi_conf_map.insert(
                name.clone(),
                Self::resolve_spi_conf(name, spi_conf_map, pin_alias_map),
            );
        }
        Ok(resolved_spi_conf_map)
    }

    fn resolve_i2c_conf(
        name: &str,
        i2c_conf_map: &HashMap<String, config::I2cConfiguration>,
    ) -> I2cConfiguration {
        if let Some(entry) = i2c_conf_map.get(name) {
            let mut conf = if let Some(ref alias_of) = entry.alias_of {
                Self::resolve_i2c_conf(alias_of.as_str(), i2c_conf_map)
            } else {
                I2cConfiguration {
                    underlying_instance: name.to_string(),
                    ..Default::default()
                }
            };
            // Apply configuration from this level
            if let Some(addr) = entry.address {
                conf.default_addr = Some(addr);
            }
            if let Some(bits_per_sec) = entry.bits_per_sec {
                conf.bits_per_sec = Some(bits_per_sec);
            }
            conf
        } else {
            I2cConfiguration {
                underlying_instance: name.to_string(),
                ..Default::default()
            }
        }
    }

    fn consolidate_i2c_conf_map(
        i2c_conf_map: &HashMap<String, config::I2cConfiguration>,
    ) -> Result<HashMap<String, I2cConfiguration>> {
        let mut resolved_i2c_conf_map = HashMap::new();
        for name in i2c_conf_map.keys() {
            resolved_i2c_conf_map.insert(name.clone(), Self::resolve_i2c_conf(name, i2c_conf_map));
        }
        Ok(resolved_i2c_conf_map)
    }

    pub fn get_interface(&self) -> &str {
        &self.interface
    }

    pub fn build_wrapper(
        self,
        transport: Box<dyn crate::transport::Transport>,
        io_mapper: Rc<IoMapper>,
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

        let mut wrapper = TransportWrapper {
            transport: Rc::from(transport),
            io_mapper,
            provides_map,
            io_expander_map: HashMap::new(),
        };

        let mut io_expanders: HashMap<String, IoExpander> = HashMap::new();
        for (name, conf) in self.io_expander_conf_map {
            io_expanders.insert(name.to_string(), ioexpander::create(&conf, &wrapper)?);
        }
        wrapper
            .io_expander_map
            .insert("NULL".to_string(), Rc::new(NullPin::new()));
        for (pinname, v) in self.pin_on_io_expander_map {
            if let Some(io) = io_expanders.get(&v.io_expander) {
                ensure!(
                    (v.pin_no as usize) < io.pins.len(),
                    TransportError::InvalidIoExpanderPinNo(v.io_expander.to_string(), v.pin_no)
                );
                wrapper
                    .io_expander_map
                    .insert(pinname, Rc::clone(&io.pins[v.pin_no as usize]));
            } else {
                bail!(TransportError::InvalidIoExpanderName(
                    v.io_expander.to_string()
                ));
            }
        }

        Ok(wrapper)
    }

    pub fn build_io_mapper(&self) -> Result<IoMapper> {
        let pin_conf_map =
            Self::consolidate_pin_conf_map(&self.pin_alias_map, &self.pin_conf_list)?;
        let mut strapping_conf_map: HashMap<String, HashMap<String, PinConfiguration>> =
            HashMap::new();
        for (strapping_name, pin_conf_map) in self.strapping_conf_map.iter() {
            strapping_conf_map.insert(
                strapping_name.clone(),
                Self::consolidate_pin_conf_map(&self.pin_alias_map, pin_conf_map)?,
            );
        }
        let spi_conf_map = Self::consolidate_spi_conf_map(&self.spi_conf_map, &self.pin_alias_map)?;
        let i2c_conf_map = Self::consolidate_i2c_conf_map(&self.i2c_conf_map)?;

        Ok(IoMapper {
            pin_map: self.pin_alias_map.clone(),
            pin_conf_map,
            uart_map: self.uart_map.clone(),
            i2c_map: self.i2c_map.clone(),
            spi_conf_map,
            i2c_conf_map,
            strapping_conf_map,
        })
    }
}

// This is the structure to be passed to each Command implementation,
// replacing the "bare" Transport argument.  The fields other than
// transport will have been computed from a number ConfigurationFiles.
pub struct TransportWrapper {
    transport: Rc<dyn Transport>,
    io_mapper: Rc<IoMapper>,
    provides_map: HashMap<String, String>,
    io_expander_map: HashMap<String, Rc<dyn GpioPin>>,
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

    pub fn get_io_expander_pin(&self, name: &str) -> Result<Rc<dyn GpioPin>> {
        let pin = self.io_mapper.resolve_pin(name);
        Ok(self
            .io_expander_map
            .get(&pin)
            .ok_or(TransportError::InvalidIoExpanderName(name.to_string()))?
            .clone())
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
        let name = name.to_uppercase();
        if let Ok(spi_conf) = self.io_mapper.spi_config(&name) {
            let wrapper = SpiWrapper::new(&*self.transport, spi_conf)?;
            Ok(Rc::new(wrapper))
        } else {
            self.transport.spi(name.as_str())
        }
    }

    /// Returns a I2C [`Bus`] implementation.
    pub fn i2c(&self, name: &str) -> Result<Rc<dyn Bus>> {
        let name = name.to_uppercase();
        if let Some(i2c_conf) = self.io_mapper.i2c_conf_map.get(&name) {
            let wrapper = I2cWrapper::new(&*self.transport, i2c_conf)?;
            Ok(Rc::new(wrapper))
        } else {
            self.transport.i2c(&name)
        }
    }

    /// Returns a [`Uart`] implementation.
    pub fn uart(&self, name: &str) -> Result<Rc<dyn Uart>> {
        self.transport
            .uart(self.io_mapper.resolve_uart(name).as_str())
    }

    /// Returns a [`GpioPin`] implementation.
    pub fn gpio_pin(&self, name: &str) -> Result<Rc<dyn GpioPin>> {
        let resolved_pin_name = self.io_mapper.resolve_pin(name);
        if let Some(pin) = self.io_expander_map.get(&resolved_pin_name) {
            return Ok(pin.clone());
        }
        self.transport.gpio_pin(name)
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
        if let Ok(strapping_conf_map) = self.io_mapper.strapping_conf(name) {
            for (pin_name, conf) in strapping_conf_map {
                pins.push(StrappedPin {
                    pin: self.gpio_pin(pin_name)?,
                    strapped: *conf,
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

    fn apply_spi_configurations(&self) -> Result<()> {
        let conf_map = &self.io_mapper.spi_conf_map;
        for (name, conf) in conf_map {
            let spi = self.spi(name.as_str())?;
            if let Some(bits_per_sec) = conf.bits_per_sec {
                spi.set_max_speed(bits_per_sec)?;
            }
        }
        Ok(())
    }

    fn apply_i2c_configurations(&self) -> Result<()> {
        let conf_map = &self.io_mapper.i2c_conf_map;
        for (name, conf) in conf_map {
            let i2c = self.i2c(name.as_str())?;
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
        self.apply_spi_configurations()?;
        self.apply_i2c_configurations()?;
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

    fn reset(&self) -> Result<()> {
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
        for StrappedPin { pin, strapped: _ } in &self.pins {
            pin.reset()?
        }
        Ok(())
    }
}

/// Several `SpiWrapper` objects can exist concurrently, sharing the same underlying transport
/// target, but e.g. having distinct chip select and clock speed settings.  (Terminology is a
/// little muddy here, the underlying object is more properly representing the SPI "bus", and this
/// wrapper a particular target chip on the bus.)
///
/// Calling e.g. `set_max_speed()` on a `SpiWrapper` will not immediately be propagated to the
/// underlying transport, instead, the accumulated settings are kept in the `SpiWrapper`, and
/// propagated only whenever an actual SPI transaction is initiated.
struct SpiWrapper {
    /// Reference to the `Target` instance of the underlying transport.
    underlying_target: Rc<dyn Target>,
    my_mode: Cell<Option<spi::TransferMode>>,
    my_bits_per_word: Cell<Option<u32>>,
    my_max_speed: Cell<Option<u32>>,
    my_chip_select: RefCell<Option<Rc<dyn GpioPin>>>,
}

impl SpiWrapper {
    fn new(transport: &dyn Transport, conf: &SpiConfiguration) -> Result<Self> {
        Ok(Self {
            underlying_target: transport.spi(conf.underlying_instance.as_str())?,
            my_mode: Cell::new(conf.mode),
            my_bits_per_word: Cell::new(conf.bits_per_word),
            my_max_speed: Cell::new(conf.bits_per_sec),
            my_chip_select: RefCell::new(match conf.chip_select {
                Some(ref cs) => Some(transport.gpio_pin(cs.as_str())?),
                None => None,
            }),
        })
    }

    fn apply_settings_to_underlying(&self) -> Result<()> {
        if let Some(mode) = self.my_mode.get() {
            self.underlying_target.set_transfer_mode(mode)?;
        }
        if let Some(bits_per_word) = self.my_bits_per_word.get() {
            self.underlying_target.set_bits_per_word(bits_per_word)?;
        }
        if let Some(max_speed) = self.my_max_speed.get() {
            self.underlying_target.set_max_speed(max_speed)?;
        }
        if let Some(chip_select) = self.my_chip_select.borrow().as_ref() {
            self.underlying_target.set_chip_select(chip_select)?;
        }
        Ok(())
    }
}

impl Target for SpiWrapper {
    fn get_transfer_mode(&self) -> Result<spi::TransferMode> {
        self.underlying_target.get_transfer_mode()
    }
    fn set_transfer_mode(&self, mode: spi::TransferMode) -> Result<()> {
        self.my_mode.set(Some(mode));
        Ok(())
    }

    fn get_bits_per_word(&self) -> Result<u32> {
        self.underlying_target.get_bits_per_word()
    }
    fn set_bits_per_word(&self, bits_per_word: u32) -> Result<()> {
        self.my_bits_per_word.set(Some(bits_per_word));
        Ok(())
    }

    fn get_max_speed(&self) -> Result<u32> {
        self.underlying_target.get_max_speed()
    }
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.my_max_speed.set(Some(max_speed));
        Ok(())
    }

    fn set_chip_select(&self, chip_select: &Rc<dyn GpioPin>) -> Result<()> {
        *self.my_chip_select.borrow_mut() = Some(Rc::clone(chip_select));
        Ok(())
    }

    fn get_max_transfer_count(&self) -> Result<usize> {
        self.underlying_target.get_max_transfer_count()
    }

    fn get_max_transfer_sizes(&self) -> Result<spi::MaxSizes> {
        self.underlying_target.get_max_transfer_sizes()
    }

    fn set_voltage(&self, voltage: crate::util::voltage::Voltage) -> Result<()> {
        self.underlying_target.set_voltage(voltage)
    }

    fn run_transaction(&self, transaction: &mut [spi::Transfer]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.underlying_target.run_transaction(transaction)
    }

    fn get_eeprom_max_transfer_sizes(&self) -> Result<spi::MaxSizes> {
        self.underlying_target.get_eeprom_max_transfer_sizes()
    }

    fn run_eeprom_transactions(&self, transactions: &mut [eeprom::Transaction]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.underlying_target.run_eeprom_transactions(transactions)
    }

    fn assert_cs(self: Rc<Self>) -> Result<spi::AssertChipSelect> {
        self.apply_settings_to_underlying()?;
        Rc::clone(&self.underlying_target).assert_cs()
    }
}

/// Several `I2cWrapper` objects can exist concurrently, sharing the same underlying transport
/// bus, but having distinct I2C 7-bit address settings.  (Terminology is a little muddy here, in
/// that the wrapper also implements the I2C "bus" trait, even though it more properly would be
/// named a "target" or "device".)
///
/// Calling e.g. `set_max_speed()` on a `I2cWrapper` will not immediately be propagated to the
/// underlying transport, instead, the accumulated settings are kept in the `I2cWrapper`, and
/// propagated only whenever an actual I2C transaction is initiated.
struct I2cWrapper {
    /// Reference to the `Bus` instance of the underlying transport.
    underlying_target: Rc<dyn Bus>,
    my_default_addr: Cell<Option<u8>>,
    my_max_speed: Cell<Option<u32>>,
}

impl I2cWrapper {
    fn new(transport: &dyn Transport, conf: &I2cConfiguration) -> Result<Self> {
        Ok(Self {
            underlying_target: transport.i2c(conf.underlying_instance.as_str())?,
            my_default_addr: Cell::new(conf.default_addr),
            my_max_speed: Cell::new(conf.bits_per_sec),
        })
    }

    fn apply_settings_to_underlying(&self) -> Result<()> {
        if let Some(addr) = self.my_default_addr.get() {
            self.underlying_target.set_default_address(addr)?;
        }
        if let Some(speed) = self.my_max_speed.get() {
            self.underlying_target.set_max_speed(speed)?;
        }
        Ok(())
    }
}

impl Bus for I2cWrapper {
    fn get_max_speed(&self) -> Result<u32> {
        self.underlying_target.get_max_speed()
    }
    fn set_max_speed(&self, max_speed: u32) -> Result<()> {
        self.my_max_speed.set(Some(max_speed));
        Ok(())
    }

    fn set_default_address(&self, addr: u8) -> Result<()> {
        self.my_default_addr.set(Some(addr));
        Ok(())
    }

    fn run_transaction(&self, addr: Option<u8>, transaction: &mut [i2c::Transfer]) -> Result<()> {
        self.apply_settings_to_underlying()?;
        self.underlying_target.run_transaction(addr, transaction)
    }
}
