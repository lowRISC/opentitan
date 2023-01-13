// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use lazy_static::lazy_static;
use regex::Regex;
use std::rc::Rc;

use crate::io::gpio::{ClockNature, Edge, GpioPin, MonitoringEvent, PinMode, PullMode};
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
    /// Reads the value of the the GPIO pin `id`.
    fn read(&self) -> Result<bool> {
        let line = self
            .inner
            .cmd_one_line_output(&format!("gpioget {}", &self.pinname))
            .map_err(|_| {
                TransportError::CommunicationError("No output from gpioget".to_string())
            })?;
        Ok(line.trim_start().starts_with('1'))
    }

    /// Sets the value of the GPIO pin `id` to `value`.
    fn write(&self, value: bool) -> Result<()> {
        self.inner
            .cmd_no_output(&format!("gpioset {} {}", &self.pinname, u32::from(value)))
    }

    fn set_mode(&self, mode: PinMode) -> Result<()> {
        self.inner.execute_command(
            &format!(
                "gpiomode {} {}",
                &self.pinname,
                match mode {
                    PinMode::Input => "input",
                    PinMode::OpenDrain => "opendrain",
                    PinMode::PushPull => "pushpull",
                    PinMode::Alternate => "alternate",
                }
            ),
            |_| {},
        )
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

    fn monitoring_start(&self) -> Result<ClockNature> {
        self.inner
            .cmd_no_output(&format!("gpio monitoring start {}", &self.pinname,))?;
        Ok(ClockNature::Wallclock {
            resolution: 1_000_000,
            offset: 0, // TODO
        })
    }

    fn monitoring_read(&self, continue_monitoring: bool) -> Result<Vec<MonitoringEvent>> {
        lazy_static! {
            pub static ref EDGE_REGEX: Regex = Regex::new("^ +([0-9]+) ([RF])").unwrap();
        }
        let mut events = Vec::new();
        self.inner.execute_command(
            &format!("gpio monitoring read {}", &self.pinname,),
            |line| {
                let Some(captures) = EDGE_REGEX.captures(line) else {
                    log::error!("Unexpected HyperDebug output: {}\n", line);
                    return;
                };
                events.push(MonitoringEvent {
                    edge: if captures.get(2).unwrap().as_str() == "R" {
                        Edge::Rising
                    } else {
                        Edge::Falling
                    },
                    timestamp: captures.get(1).unwrap().as_str().parse().unwrap(),
                });
            },
        )?;
        if !continue_monitoring {
            self.inner
                .cmd_no_output(&format!("gpio monitoring stop {}", &self.pinname,))?;
        }
        Ok(events)
    }
}
