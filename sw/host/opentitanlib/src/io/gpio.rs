// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::ValueEnum;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::impl_serializable_error;
use crate::transport::TransportError;

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

impl PinConfiguration {
    /// Sometimes one configuration file specifies OpenDrain while leaving out the level, and
    /// another file specifies high level, while leaving out the mode.  This method will merge
    /// declarations from multiple files, as long as they are not conflicting (e.g. both PushPull
    /// and OpenDrain, or both high and low level.)
    pub fn merge(&mut self, other: &PinConfiguration) -> Option<()> {
        super::merge_configuration_field(&mut self.mode, &other.mode)?;
        super::merge_configuration_field(&mut self.level, &other.level)?;
        super::merge_configuration_field(&mut self.pull_mode, &other.pull_mode)?;
        super::merge_configuration_field(&mut self.volts, &other.volts)
    }
}

/// Errors related to the GPIO interface.
#[derive(Debug, Error, Serialize, Deserialize)]
pub enum GpioError {
    #[error("Invalid pin name {0}")]
    InvalidPinName(String),
    #[error("Invalid pin number {0}")]
    InvalidPinNumber(u8),
    /// The current mode of the pin (input) does not support the requested operation (set
    /// level).
    #[error("Invalid mode for pin {0}")]
    InvalidPinMode(u8),
    /// The hardware does not support the requested mode (open drain, pull down input, etc.)
    #[error("Unsupported mode {0} requested")]
    UnsupportedPinMode(PinMode),
    /// The hardware does not support the requested mode (open drain, pull down input, etc.)
    #[error("Unsupported pull mode {0} requested")]
    UnsupportedPullMode(PullMode),
    #[error("Conflicting pin configurations for pin {0}: host:{1}, target:{2}")]
    PinModeConflict(String, String, String),
    #[error("Conflicting pin logic values for pin {0}: host:{1}, target:{2}")]
    PinValueConflict(String, String, String),
    #[error("Undefined pin logic value for pin {0}")]
    PinValueUndefined(String),
    #[error("Unsupported voltage {0}V requested")]
    UnsupportedPinVoltage(f32),
    #[error("Generic error: {0}")]
    Generic(String),
}
impl_serializable_error!(GpioError);

/// Mode of I/O pins.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "verbatim")]
pub enum PinMode {
    Input,
    PushPull,
    OpenDrain,
    AnalogInput,
    AnalogOutput,
    Alternate, // Pin used for UART/SPI/I2C or something else
}

impl std::fmt::Display for PinMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

/// Mode of weak pull (relevant in Input and OpenDrain modes).
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq, ValueEnum)]
#[value(rename_all = "verbatim")]
pub enum PullMode {
    None,
    PullUp,
    PullDown,
}

impl std::fmt::Display for PullMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(self, f)
    }
}

/// A trait which represents a single GPIO pin.
pub trait GpioPin {
    /// Reads the value of the GPIO pin.
    fn read(&self) -> Result<bool>;

    /// Sets the value of the GPIO pin to `value`.
    fn write(&self, value: bool) -> Result<()>;

    /// Sets the mode of the GPIO pin as input, output, or open drain I/O.
    fn set_mode(&self, mode: PinMode) -> Result<()>;

    /// Sets the weak pull resistors of the GPIO pin.
    fn set_pull_mode(&self, mode: PullMode) -> Result<()>;

    /// Reads the analog value of the GPIO pin in Volts. `AnalogInput` mode disables digital
    /// circuitry for better results, but this method may also work in other modes.
    fn analog_read(&self) -> Result<f32> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Sets the analog value of the GPIO pin to `value` Volts, must be in `AnalogOutput` mode.
    fn analog_write(&self, _volts: f32) -> Result<()> {
        Err(TransportError::UnsupportedOperation.into())
    }

    /// Simultaneously sets mode, value, and weak pull, some transports may guarantee atomicity.
    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        analog_value: Option<f32>,
    ) -> Result<()> {
        // Transports must override this function for truly atomic behavior.  Default
        // implementation below applies each setting separately.
        if let Some(mode) = mode {
            self.set_mode(mode)?;
        }
        if let Some(pull) = pull {
            self.set_pull_mode(pull)?;
        }
        if let Some(value) = value {
            self.write(value)?;
        }
        if let Some(analog_value) = analog_value {
            self.analog_write(analog_value)?;
        }
        Ok(())
    }

    /// Reset pin level to the default value.
    fn reset(&self) -> Result<()>;

    /// Not meant for API clients, this method returns the pin name as it is known to the
    /// transport (which may have been through one or more alias mappings from the name provided
    /// by the API client.)  This method is used by implementations of `GpioMonitoring`.
    fn get_internal_pin_name(&self) -> Option<&str> {
        None
    }
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum Edge {
    Rising,
    Falling,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub enum ClockNature {
    /// Unix time can be computed as (t + offset) / resolution, where t is a 64-bit timestamp
    /// value from `MonitoringEvent`.
    Wallclock {
        /// If resolution is microseconds, `resolution` will be 1_000_000.
        resolution: u64,
        /// Offset relative to Unix epoch, measured according to above resolution.
        offset: Option<u64>,
    },
    /// The 64-bit timestamp values could be emulator clock counts, or some other measure that
    /// increases monotonically, but not necessarily uniformly in relation to wall clock time.
    Unspecified,
}

/// Represents an edge detected on the GPIO pin.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub struct MonitoringEvent {
    /// Identification of the signal that had an event, in the form of an index into the array
    /// originally passed to `monitoring_read()`.
    pub signal_index: u8,
    /// Rising or falling edge
    pub edge: Edge,
    /// Timestamp of the edge, resolution and epoch is transport-specific, more information in
    /// `ClockNature`.
    pub timestamp: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MonitoringStartResponse {
    /// Transport timestamp at the time monitoring started.
    pub timestamp: u64,
    /// Initial logic level for each of the given pins.
    pub initial_levels: Vec<bool>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MonitoringReadResponse {
    /// List of events having occurred since the start or the last read.
    pub events: Vec<MonitoringEvent>,
    /// All events at or before this timestamp are guaranteed to be included.
    pub timestamp: u64,
}

/// A trait implemented by transports which support advanced edge-detection on GPIO pins.  This
/// trait allows monitoring a set of pins, and getting a stream of "events" (rising and falling
/// edges with timestamps) for any change among the set.
pub trait GpioMonitoring {
    fn get_clock_nature(&self) -> Result<ClockNature>;

    /// Set up edge trigger detection on the given set of pins, transport will buffer the list
    /// internally, return the initial level of each of the given pins.
    fn monitoring_start(&self, pins: &[&dyn GpioPin]) -> Result<MonitoringStartResponse>;

    /// Retrieve list of events detected thus far, optionally stopping the possibly expensive edge
    /// detection.  Buffer overrun will be reported as an `Err`, and result in the stopping of the
    /// edge detection irrespective of the parameter value.
    fn monitoring_read(
        &self,
        pins: &[&dyn GpioPin],
        continue_monitoring: bool,
    ) -> Result<MonitoringReadResponse>;
}
