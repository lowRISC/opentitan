// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::ValueEnum;
use serde::{Deserialize, Serialize};
use std::time::Duration;
use thiserror::Error;

use crate::impl_serializable_error;
use crate::transport::TransportError;

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
    #[error("Unsupported number of pins: {0}")]
    UnsupportedNumberOfPins(usize),
    #[error("Mismatched bitbang data length: {0} != {1}")]
    MismatchedDataLength(usize, usize),
    #[error("Bitbang data beyond the {0} least significant bits")]
    InvalidBitbangData(usize),
    #[error("Bitbang delay of zero, immediately preceding `await()`, or at end of sequence, not permitted")]
    InvalidBitbangDelay,
    #[error("Dac-bang samples not a multiple of number of pins")]
    InvalidDacBangData,
    #[error("Dac-bang delay of zero or immediately adjacent to linear(), or at end of sequence, not permitted")]
    InvalidDacBangDelay,
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

/// Represents one entry in the specification of a bitbanging waveform.  Pins must have been
/// configured as either `PushPull`, `OpenDrain` or `Input` prior to requesting a bitbang
/// operation.
///
/// `Write` and `Both` are somewhat equivalent to their namesakes in `spi::Transfer`, that is
/// `Write` requests using the given data for generating waveforms on any of the pins configured
/// as output, while disregarding the actual levels of the pins.  `Both` requests generating a
/// waveform, and also sampling every pin at each clock tick.
pub enum BitbangEntry<'rd, 'wr> {
    /// Represents a sequence of pin values.  Bit 0 in each byte controls the first `GpioPin` in
    /// the slice given to `GpioBitbanging::run()`, bit 1 controls the second `GpioPin`, and so
    /// on.  Each byte is applied to the pins in sequence, with a particular delay between each
    /// given by the `clock_tick` argument to `run()`.
    Write(&'wr [u8]),
    /// Same as `Write`, but this `BitbangEntry` owns the data.
    WriteOwned(Box<[u8]>),
    /// Represents a sequence of pin values as above, but additionally captures the value of any
    /// pins in `Input` or `OpenDrain` mode.  At each clock tick, the input levels are sampled
    /// just before the given output levels are applied, meaning that the data coming back will be
    /// offset by one sample.
    Both(&'wr [u8], &'rd mut [u8]),
    /// Same as `Both`, but this `BitbangEntry` owns the data, which will be overwritten.
    BothOwned(Box<[u8]>),
    /// Represents a delay of the given number of clock ticks in which the output levels are held
    /// as indicated by the last byte of the preceding `Write`/`Both` entry.
    ///
    /// A delay of zero is invalid.  A delay of one tick is equivalent to not specifying any
    /// `Delay` between two `Write` blocks, which is also equivalent to concatenating the two into
    /// a single `Write` block.
    Delay(u32),
    /// Similar to `Delay`, but waits until `(pin_values ^ pattern) & mask` equals zero, that is,
    /// until the set of pins indicated by ones in `mask` all have the the value indicated in
    /// `pattern`.
    Await { mask: u8, pattern: u8 },
}

pub enum DacBangEntry<'wr> {
    /// Represents a sequence of volt values.  If `N` pin is being driven, then samples are
    /// interleaved such that at first, the first `N` values are applied, one to each of the pins,
    /// at next tick the next `N` values are applied, and so on, with a particular delay between
    /// each tick given by the `clock_tick` argument to `run()`.
    Write(&'wr [f32]),
    /// Same as `Write`, but this `DacBangEntry` owns the data.
    WriteOwned(Box<[f32]>),
    /// Represents a delay of the given number of clock ticks in which the output levels are held
    /// as indicated by the last values of the preceding `Write` entry.
    ///
    /// A delay of zero is invalid.  A delay of one tick is equivalent to not specifying any
    /// `Delay` between two `Write` blocks, which is also equivalent to concatenating the two into
    /// a single `Write` block.
    Delay(u32),
    /// Represents a time span of the given number of clock ticks during which the voltage
    /// linearly transitions from the previous to the subsequent value.
    ///
    /// A value of zero is invalid.  A value of one tick is equivalent to not specifying any delay
    /// between two `Write` blocks.  A value of two will result in a single intermediate sample
    /// halfway between the two voltages.  In general, a value of N will result in N-1
    /// intermediate samples being inserted at this point.
    Linear(u32),
}

/// A trait implemented by transports which support synchronous bit-banging on GPIO pins, similar
/// to FTDI devices.  This trait allows generation of arbitrary waveforms on a set of pins, and
/// optionally getting back samples from same or other pins, taken at precise times.
pub trait GpioBitbanging {
    /// Apply the given sequence of values to the given set of GPIO pins, by each tick of a clock
    /// with the given period.  This function does not change the mode of any pins, they must
    /// already be put into `PushPull`, `OpenDrain` or `Input` mode as appropriate.  (In the
    /// latter case, the specified waveform data does not matter, as the pin is not driving, and
    /// would be included in the set of pins only in order to have it sampled at each clock tick.)
    /// Returns a `GpioBitbangOperation` which must be continuously polled, to know when the
    /// waveform is complete.
    fn start<'a>(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: Box<[BitbangEntry<'a, 'a>]>,
    ) -> Result<Box<dyn GpioBitbangOperation<'a, 'a> + 'a>>;

    /// Convenience method which starts the bitbanging operation, and blocks until it is complete.
    fn run<'a>(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: Box<[BitbangEntry<'a, 'a>]>,
    ) -> Result<Box<[BitbangEntry<'a, 'a>]>> {
        let mut bitbang_op = self.start(pins, clock_tick, waveform)?;
        while !bitbang_op.query()? {}
        bitbang_op.get_result()
    }

    /// Apply given sequence of voltage values to the given set of pins assumed to already be in
    /// AnalogOutput mode.
    fn dac_start(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: Box<[DacBangEntry]>,
    ) -> Result<Box<dyn GpioDacBangOperation>>;

    /// Convenience method which starts the DAC-banging operation, and blocks until it is
    /// complete.
    fn dac_run(
        &self,
        pins: &[&dyn GpioPin],
        clock_tick: Duration,
        waveform: Box<[DacBangEntry]>,
    ) -> Result<()> {
        let mut dacbang_op = self.dac_start(pins, clock_tick, waveform)?;
        while !dacbang_op.query()? {}
        Ok(())
    }
}

/// Object representing an ongoing operation of generating a prescribed waveform on a number of
/// pins.  Must be frequently polled via the `query()` function, in order to guerantee completion
/// of the operation.
pub trait GpioBitbangOperation<'rd, 'wr> {
    /// Returns `true` when done, `false` means to call it again.
    fn query(&mut self) -> Result<bool>;

    /// After `query()` has returned `true`, this method can be called to get back the array of
    /// `BitbangEntry` originally given, this is particularly useful if there are `WriteOwned` or
    /// `BothOwned` among the entries of the array.
    fn get_result(self: Box<Self>) -> Result<Box<[BitbangEntry<'rd, 'wr>]>>;
}

pub trait GpioDacBangOperation {
    /// Returns `true` when done, `false` means to call it again.
    fn query(&mut self) -> Result<bool>;
}
