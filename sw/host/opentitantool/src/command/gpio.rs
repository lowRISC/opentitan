// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use is_terminal::IsTerminal;
use raw_tty::TtyModeGuard;
use serde_annotate::Annotate;
use std::any::Any;
use std::borrow::Borrow;
use std::fs::File;
use std::io::{Read, Write};
use std::os::unix::io::AsRawFd;
use std::rc::Rc;
use std::str::FromStr;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::{ClockNature, Edge, GpioPin, PinMode, PullMode};
use opentitanlib::transport::Capability;
use opentitanlib::util::file;
use opentitanlib::util::voltage::Voltage;

#[derive(Debug, Args)]
/// Reads a GPIO pin.
pub struct GpioRead {
    #[arg(name = "PIN", help = "The GPIO pin to read")]
    pub pin: String,
}

#[derive(serde::Serialize)]
pub struct GpioReadResult {
    pub pin: String,
    pub value: bool,
}

impl CommandDispatch for GpioRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        let value = gpio_pin.read()?;
        Ok(Some(Box::new(GpioReadResult {
            pin: self.pin.clone(),
            value,
        })))
    }
}

#[derive(Debug, Args)]
/// Writes a GPIO pin.
pub struct GpioWrite {
    #[arg(name = "PIN", help = "The GPIO pin to write")]
    pub pin: String,
    #[arg(
        name = "VALUE",
        action = clap::ArgAction::Set,
        help = "The value to write to the pin"
    )]
    pub value: bool,
}

impl CommandDispatch for GpioWrite {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;

        gpio_pin.write(self.value)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Set the I/O mode of a GPIO pin (Input/OpenDrain/PushPull).
pub struct GpioSetMode {
    #[arg(name = "PIN", help = "The GPIO pin to modify")]
    pub pin: String,
    #[arg(
        name = "MODE",
        value_enum,
        ignore_case = true,
        help = "The I/O mode of the pin"
    )]
    pub mode: PinMode,
}

impl CommandDispatch for GpioSetMode {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        gpio_pin.set_mode(self.mode)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Set the I/O weak pull mode of a GPIO pin (PullUp/PullDown/None).
pub struct GpioSetPullMode {
    #[arg(name = "PIN", help = "The GPIO pin to modify")]
    pub pin: String,
    #[arg(
        name = "PULLMODE",
        value_enum,
        ignore_case = true,
        help = "The weak pull mode of the pin"
    )]
    pub pull_mode: PullMode,
}

impl CommandDispatch for GpioSetPullMode {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        gpio_pin.set_pull_mode(self.pull_mode)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Simultaneously set mode, pull and output value of a GPIO pin.
pub struct GpioSet {
    #[arg(name = "PIN", help = "The GPIO pin to modify")]
    pub pin: String,
    #[arg(long, ignore_case = true, help = "The I/O mode of the pin")]
    pub mode: Option<PinMode>,
    #[arg(
        long,
        value_parser = bool::from_str,
        help = "The value to write to the pin, has effect only in PushPull and OpenDrain modes"
    )]
    pub value: Option<bool>,
    #[arg(long, ignore_case = true, help = "The weak pull mode of the pin")]
    pub pull: Option<PullMode>,
    #[arg(
        long,
        value_parser = bool::from_str,
        help = "The analog value to write to the pin in volts, has effect only in AnalogOutput mode"
    )]
    pub voltage: Option<Voltage>,
}

impl CommandDispatch for GpioSet {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;

        gpio_pin.set(
            self.mode,
            self.value,
            self.pull,
            self.voltage.map(|v| v.as_volts() as f32),
        )?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Reads a GPIO pin.
pub struct GpioAnalogRead {
    #[arg(name = "PIN", help = "The GPIO pin to read")]
    pub pin: String,
}

#[derive(serde::Serialize)]
pub struct GpioAnalogReadResult {
    pub pin: String,
    pub volts: f32,
}

impl CommandDispatch for GpioAnalogRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;
        let volts = gpio_pin.analog_read()?;
        Ok(Some(Box::new(GpioAnalogReadResult {
            pin: self.pin.clone(),
            volts,
        })))
    }
}

#[derive(Debug, Args)]
/// Writes an analog voltage to a GPIO pin.
pub struct GpioAnalogWrite {
    #[arg(name = "PIN", help = "The GPIO pin to write")]
    pub pin: String,
    #[arg(
        name = "VOLTS",
        value_parser = bool::from_str,
        help = "The analog value to write to the pin in volts, has effect only in AnalogOutput mode"
    )]
    pub volts: f32,
}

impl CommandDispatch for GpioAnalogWrite {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;

        gpio_pin.analog_write(self.volts)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Apply a configuration-named pin strapping
pub struct GpioApplyStrapping {
    #[arg(name = "NAME", help = "The pin strapping to apply")]
    pub name: String,
}

impl CommandDispatch for GpioApplyStrapping {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        transport.pin_strapping(&self.name)?.apply()?;
        Ok(None)
    }
}

#[derive(Debug, Subcommand, CommandDispatch)]
pub enum GpioMonitoringCommand {
    Start(GpioMonitoringStart),
    Read(GpioMonitoringRead),
    Vcd(GpioMonitoringVcd),
}

#[derive(Debug, Args)]
/// Begin logic-analyzer style monitoring of a set of pins.
pub struct GpioMonitoringStart {
    #[arg(
        name = "PINS",
        help = "The list of GPIO pins to monitor (space separated)"
    )]
    pub pins: Vec<String>,
}

#[derive(serde::Serialize)]
pub struct InitialLevel {
    pub signal_name: String,
    pub value: bool,
}

#[derive(serde::Serialize)]
pub struct GpioMonitoringStartResult {
    pub clock_nature: ClockNature,
    pub timestamp: u64,
    pub initial_levels: Vec<InitialLevel>,
}

impl CommandDispatch for GpioMonitoringStart {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport
            .capabilities()?
            .request(Capability::GPIO | Capability::GPIO_MONITORING)
            .ok()?;
        let gpio_monitoring = transport.gpio_monitoring()?;
        let gpio_pins = transport.gpio_pins(&self.pins)?;
        let clock_nature = gpio_monitoring.get_clock_nature()?;
        let resp = gpio_monitoring.monitoring_start(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
        )?;
        Ok(Some(Box::new(GpioMonitoringStartResult {
            clock_nature,
            initial_levels: resp
                .initial_levels
                .into_iter()
                .enumerate()
                .map(|(i, l)| InitialLevel {
                    signal_name: self.pins[i].clone(),
                    value: l,
                })
                .collect(),
            timestamp: resp.timestamp,
        })))
    }
}

#[derive(Debug, Args)]
/// Retrieve logic-analyzer style monitoring events detected so far, on a set of pins.  Optionally
/// continue monitoring, in which case `monitoring read` must be called again later.
pub struct GpioMonitoringRead {
    #[arg(
        name = "PINS",
        help = "The list of GPIO pins being monitored (space separated)"
    )]
    pub pins: Vec<String>,

    #[arg(long, ignore_case = true)]
    pub continue_monitoring: bool,
}

#[derive(serde::Serialize)]
pub struct MonitoringEvent {
    pub signal_name: String,
    pub edge: Edge,
    /// Timestamp of the edge, resolution and epoch is transport-specific.
    pub timestamp: u64,
}

#[derive(serde::Serialize)]
pub struct GpioMonitoringReadResult {
    /// List of events that has happened since last queried.
    pub events: Vec<MonitoringEvent>,
    /// Timestamp of the reading, all events happening before this time are guaranteed to be
    /// included in the list above.
    pub timestamp: u64,
}

impl CommandDispatch for GpioMonitoringRead {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport
            .capabilities()?
            .request(Capability::GPIO | Capability::GPIO_MONITORING)
            .ok()?;
        let gpio_monitoring = transport.gpio_monitoring()?;
        let gpio_pins = transport.gpio_pins(&self.pins)?;
        let resp = gpio_monitoring.monitoring_read(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
            self.continue_monitoring,
        )?;
        Ok(Some(Box::new(GpioMonitoringReadResult {
            events: resp
                .events
                .into_iter()
                .map(|e| MonitoringEvent {
                    signal_name: self.pins[e.signal_index as usize].clone(),
                    edge: e.edge,
                    timestamp: e.timestamp,
                })
                .collect(),
            timestamp: resp.timestamp,
        })))
    }
}

#[derive(Debug, Args)]
/// Whereas `monitoring start` and `monitoring read` are meant for use by scripts, this
/// `monitoring vcd` is intended for manual use by an operator.  It will stay in the foreground,
/// collecting events until the user presses Ctrl-C.  A transcript will be written in the industry
/// standard VCD format, which can be loaded into e.g. Pulseview (or probably also Saleae
/// software), to get a logic analyzer view of what transpired.
pub struct GpioMonitoringVcd {
    #[arg(
        name = "PINS",
        help = "The list of GPIO pins to monitor (space separated)"
    )]
    pub pins: Vec<String>,

    #[arg(short, long, help = "Output file")]
    outfile: String,

    #[arg(short, long, help = "Do not print start end exit messages.")]
    quiet: bool,
}

impl CommandDispatch for GpioMonitoringVcd {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport
            .capabilities()?
            .request(Capability::GPIO | Capability::GPIO_MONITORING)
            .ok()?;
        let gpio_monitoring = transport.gpio_monitoring()?;
        let gpio_pins = transport.gpio_pins(&self.pins)?;
        let mut file = File::create(&self.outfile)?;

        if !self.quiet {
            eprintln!("Dumping events to {}", &self.outfile);
            eprint!("[CTRL+C] to exit  ");
        }
        // Putting the terminal input into raw mode is the only way we can catch Ctrl-C.  (This is
        // not ideal, it would have been better to catch the SIGINT signal, but the mio_signals
        // package is not compatible with the way that our rusb library uses background threads.)
        // The tty guard will restore the console settings when it goes out of scope.
        let mut stdin = std::io::stdin();
        let _stdin_guard = if stdin.is_terminal() {
            let mut guard = TtyModeGuard::new(stdin.as_raw_fd())?;
            guard.set_raw_mode()?;
            Some(guard)
        } else {
            None
        };

        // Inform the transport that we want to monitor a set of pins, and write a file header
        // with the names of each of the monitored signals.
        let clock_nature = gpio_monitoring.get_clock_nature()?;
        let initial = gpio_monitoring.monitoring_start(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
        )?;
        writeln!(&mut file, "$version")?;
        let version = super::version::VersionResponse::default();
        writeln!(
            &mut file,
            "   opentitantool {} {} {}",
            version.version,
            if version.clean { "clean" } else { "modified" },
            version.timestamp,
        )?;
        writeln!(&mut file, "$end")?;
        match clock_nature {
            ClockNature::Wallclock { resolution, .. } => {
                writeln!(
                    &mut file,
                    "$timescale {}ps $end",
                    1000000000000u64 / resolution
                )?;
            }
            ClockNature::Unspecified => (),
        }
        writeln!(&mut file, "$scope module logic $end")?;
        for (n, pin) in self.pins.iter().enumerate() {
            writeln!(&mut file, "$var wire 1 '{} {} $end", n, pin)?;
        }
        writeln!(&mut file, "$upscope $end")?;
        writeln!(&mut file, "$enddefinitions $end")?;
        writeln!(&mut file, "#{}", initial.timestamp)?;
        for (n, v) in initial.initial_levels.iter().enumerate() {
            writeln!(&mut file, "{}'{}", if *v { 1 } else { 0 }, n)?;
        }

        // Now loop indefinitely, retrieving events from the internal queue of the transport and
        // printing them to the output file.
        let mut loop_count: usize = 0;
        'event_loop: loop {
            let resp = gpio_monitoring.monitoring_read(
                &gpio_pins
                    .iter()
                    .map(Rc::borrow)
                    .collect::<Vec<&dyn GpioPin>>(),
                true,
            )?;
            for event in &resp.events {
                writeln!(&mut file, "#{}", event.timestamp)?;
                writeln!(
                    &mut file,
                    "{}'{}",
                    match event.edge {
                        Edge::Rising => 1,
                        Edge::Falling => 0,
                    },
                    event.signal_index
                )?;
            }
            eprint!("\u{8}{}", ['/', '-', '\\', '|'][loop_count & 3usize]);
            let delay = if resp.events.is_empty() {
                Duration::from_millis(10)
            } else {
                Duration::from_millis(0)
            };
            if file::wait_fd_read_timeout(stdin.as_raw_fd(), delay).is_ok() {
                let mut buf = [0u8; 1];
                let len = stdin.read(&mut buf)?;
                if len == 1 && buf[0] == 3 {
                    // CtrlC
                    break 'event_loop;
                }
            }
            loop_count += 1;
        }

        // Make one final reading to fetch any events that may have happened just before user
        // requested to end monitoring.
        let resp = gpio_monitoring.monitoring_read(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
            false,
        )?;
        for event in &resp.events {
            writeln!(&mut file, "#{}", event.timestamp)?;
            writeln!(
                &mut file,
                "{}'{}",
                match event.edge {
                    Edge::Rising => 1,
                    Edge::Falling => 0,
                },
                event.signal_index
            )?;
        }
        // Output timestamp of final reading (all signals remained stable from the last edge until
        // this time.)
        writeln!(&mut file, "#{}", resp.timestamp)?;
        eprintln!("\r");
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Remove a configuration-named pin strapping
pub struct GpioRemoveStrapping {
    #[arg(name = "NAME", help = "The pin strapping to release")]
    pub name: String,
}

impl CommandDispatch for GpioRemoveStrapping {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        transport.pin_strapping(&self.name)?.remove()?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
pub struct GpioMonitoring {
    #[command(subcommand)]
    command: GpioMonitoringCommand,
}

impl CommandDispatch for GpioMonitoring {
    fn run(
        &self,
        context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        self.command.run(context, transport)
    }
}

/// Commands for manipulating GPIO pins.
#[derive(Debug, Subcommand, CommandDispatch)]
pub enum GpioCommand {
    Apply(GpioApplyStrapping),
    Remove(GpioRemoveStrapping),
    Read(GpioRead),
    Write(GpioWrite),
    SetMode(GpioSetMode),
    SetPullMode(GpioSetPullMode),
    Set(GpioSet),
    AnalogRead(GpioAnalogRead),
    AnalogWrite(GpioAnalogWrite),
    Monitoring(GpioMonitoring),
}
