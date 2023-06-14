// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use once_cell::sync::Lazy;
use regex::Regex;
use std::rc::Rc;

use crate::io::gpio::{
    ClockNature, Edge, GpioError, GpioMonitoring, GpioPin, MonitoringEvent, MonitoringReadResponse,
    MonitoringStartResponse, PinMode, PullMode,
};
use crate::transport::hyperdebug::Inner;
use crate::transport::TransportError;

pub struct HyperdebugGpioPin {
    inner: Rc<Inner>,
    pinname: String,
}

impl HyperdebugGpioPin {
    pub fn open(inner: &Rc<Inner>, pinname: &str) -> Result<Self> {
        let result = Self {
            inner: Rc::clone(inner),
            pinname: pinname.to_string(),
        };
        Ok(result)
    }
}

impl GpioPin for HyperdebugGpioPin {
    /// Reads the value of the GPIO pin `id`.
    fn read(&self) -> Result<bool> {
        let line = self
            .inner
            .cmd_one_line_output(&format!("gpioget {}", &self.pinname))?;
        Ok(line.trim_start().starts_with('1'))
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.inner
            .cmd_no_output(&format!("gpioset {} {}", &self.pinname, u32::from(value)))
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        self.inner.cmd_no_output(&format!(
            "gpiomode {} {}",
            &self.pinname,
            match mode {
                PinMode::Input => "input",
                PinMode::OpenDrain => "opendrain",
                PinMode::PushPull => "pushpull",
                PinMode::AnalogInput => "adc",
                PinMode::AnalogOutput => "dac",
                PinMode::Alternate => "alternate",
            }
        ))
    }

    fn set_pull_mode(&self, mode: PullMode) -> Result<()> {
        self.inner.cmd_no_output(&format!(
            "gpiopullmode {} {}",
            &self.pinname,
            match mode {
                PullMode::None => "none",
                PullMode::PullUp => "up",
                PullMode::PullDown => "down",
            }
        ))
    }

    fn analog_read(&self) -> Result<f32> {
        let line = self
            .inner
            .cmd_one_line_output(&format!("adc {}", &self.pinname))
            .map_err(|_| TransportError::CommunicationError("No output from adc".to_string()))?;
        static ADC_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new("^ +([^ ])+ = ([0-9]+) mV").unwrap());
        if let Some(captures) = ADC_REGEX.captures(&line) {
            let milli_volts: u32 = captures.get(2).unwrap().as_str().parse()?;
            Ok(milli_volts as f32 / 1000.0)
        } else {
            Err(TransportError::CommunicationError("Unrecognized adc output".to_string()).into())
        }
    }

    fn analog_write(&self, volts: f32) -> Result<()> {
        if !(0.0..=3.3).contains(&volts) {
            return Err(GpioError::UnsupportedPinVoltage(volts).into());
        }
        let milli_volts = (volts * 1000.0) as u32;
        self.inner.cmd_no_output(&format!(
            "gpio analog-set {} {}",
            &self.pinname, milli_volts,
        ))
    }

    fn set(
        &self,
        mode: Option<PinMode>,
        value: Option<bool>,
        pull: Option<PullMode>,
        volts: Option<f32>,
    ) -> Result<()> {
        if let Some(v) = volts {
            if !(0.0..=3.3).contains(&v) {
                return Err(GpioError::UnsupportedPinVoltage(v).into());
            }
        }
        self.inner
            .cmd_no_output(&format!(
                "gpio multiset {} {} {} {} {}",
                &self.pinname,
                match value {
                    Some(false) => "0",
                    Some(true) => "1",
                    None => "-",
                },
                match mode {
                    Some(PinMode::Input) => "input",
                    Some(PinMode::OpenDrain) => "opendrain",
                    Some(PinMode::PushPull) => "pushpull",
                    Some(PinMode::AnalogInput) => "adc",
                    Some(PinMode::AnalogOutput) => "dac",
                    Some(PinMode::Alternate) => "alternate",
                    None => "-",
                },
                match pull {
                    Some(PullMode::None) => "none",
                    Some(PullMode::PullUp) => "up",
                    Some(PullMode::PullDown) => "down",
                    None => "-",
                },
                if let Some(v) = volts {
                    format!("{}", (v * 1000.0) as u32)
                } else {
                    "-".to_string()
                },
            ))
            .or_else(|_| {
                // HyperDebug firmware does not support atomically setting all three, fall back to
                // separate commands.
                if let Some(mode) = mode {
                    self.set_mode(mode)?;
                }
                if let Some(pull) = pull {
                    self.set_pull_mode(pull)?;
                }
                if let Some(value) = value {
                    self.write(value)?;
                }
                if let Some(volts) = volts {
                    self.analog_write(volts)?;
                }
                Ok(())
            })
    }

    fn get_internal_pin_name(&self) -> Option<&str> {
        Some(&self.pinname)
    }
}

pub struct HyperdebugGpioMonitoring {
    inner: Rc<Inner>,
}

impl HyperdebugGpioMonitoring {
    pub fn open(inner: &Rc<Inner>) -> Result<Self> {
        Ok(Self {
            inner: Rc::clone(inner),
        })
    }
}

impl GpioMonitoring for HyperdebugGpioMonitoring {
    fn get_clock_nature(&self) -> Result<ClockNature> {
        Ok(ClockNature::Wallclock {
            resolution: 1_000_000,
            offset: None,
        })
    }

    /// Set up edge trigger detection on the given set of pins, transport will buffer the list
    /// internally.
    fn monitoring_start(&self, pins: &[&dyn GpioPin]) -> Result<MonitoringStartResponse> {
        let mut pin_names = Vec::new();
        for pin in pins {
            pin_names.push(
                pin.get_internal_pin_name()
                    .ok_or(TransportError::InvalidOperation)?,
            );
        }
        static START_TIME_REGEX: Lazy<Regex> = Lazy::new(|| Regex::new("^ +@([0-9]+)").unwrap());
        static SIGNAL_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new("^ +([0-9]+) ([^ ])+ ([01])").unwrap());
        let mut start_time: u64 = 0;
        let mut signals = Vec::new();
        let mut unexpected_output = false;
        self.inner.execute_command(
            &format!("gpio monitoring start {}", pin_names.join(" ")),
            |line| {
                if let Some(captures) = START_TIME_REGEX.captures(line) {
                    start_time = captures.get(1).unwrap().as_str().parse().unwrap();
                } else if let Some(captures) = SIGNAL_REGEX.captures(line) {
                    signals.push(captures.get(3).unwrap().as_str() != "0");
                } else {
                    unexpected_output = true;
                    log::error!("Unexpected HyperDebug output: {}\n", line);
                };
            },
        )?;
        if unexpected_output {
            bail!(TransportError::CommunicationError(
                "Unrecognized response".to_string()
            ))
        }
        Ok(MonitoringStartResponse {
            timestamp: start_time,
            initial_levels: signals,
        })
    }

    /// Retrieve list of events detected thus far, optionally stopping the possibly expensive edge
    /// detection.  Buffer overrun will be reported as an `Err`, and result in the stopping of the
    /// edge detection irrespective of the parameter value.
    fn monitoring_read(
        &self,
        pins: &[&dyn GpioPin],
        continue_monitoring: bool,
    ) -> Result<MonitoringReadResponse> {
        let mut pin_names = Vec::new();
        for pin in pins {
            pin_names.push(
                pin.get_internal_pin_name()
                    .ok_or(TransportError::InvalidOperation)?,
            );
        }
        static START_TIME_REGEX: Lazy<Regex> = Lazy::new(|| Regex::new("^ +@([0-9]+)").unwrap());
        static EDGE_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new("^ +([0-9]+) (-?[0-9]+) ([RF])").unwrap());
        let mut reference_time: u64 = 0;
        let mut events = Vec::new();
        loop {
            let mut more_data = false;
            let mut unexpected_output = false;
            self.inner.execute_command(
                &format!("gpio monitoring read {}", pin_names.join(" ")),
                |line| {
                    if let Some(captures) = START_TIME_REGEX.captures(line) {
                        reference_time = captures.get(1).unwrap().as_str().parse().unwrap();
                    } else if let Some(captures) = EDGE_REGEX.captures(line) {
                        events.push(MonitoringEvent {
                            signal_index: captures.get(1).unwrap().as_str().parse().unwrap(),
                            edge: if captures.get(3).unwrap().as_str() == "R" {
                                Edge::Rising
                            } else {
                                Edge::Falling
                            },
                            timestamp: (reference_time as i64
                                + captures.get(2).unwrap().as_str().parse::<i64>().unwrap())
                                as u64,
                        });
                    } else if line == "Warning: more data" {
                        more_data = true;
                    } else {
                        unexpected_output = true;
                        log::error!("Unexpected HyperDebug output: {}\n", line);
                    }
                },
            )?;
            if unexpected_output {
                bail!(TransportError::CommunicationError(
                    "Unrecognized response".to_string()
                ))
            }
            if !more_data {
                break;
            }
        }
        if !continue_monitoring {
            self.inner
                .cmd_no_output(&format!("gpio monitoring stop {}", pin_names.join(" ")))?;
        }
        Ok(MonitoringReadResponse {
            events,
            timestamp: reference_time, // TODO: adjust in case of event later than this timestamp
        })
    }
}
