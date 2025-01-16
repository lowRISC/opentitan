// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use clap::{Args, Subcommand};
use serde_annotate::Annotate;
use std::any::Any;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::fs::File;
use std::io::{Read, Write};
use std::rc::Rc;
use std::str::FromStr;
use std::time::Duration;

use opentitanlib::app::command::CommandDispatch;
use opentitanlib::app::TransportWrapper;
use opentitanlib::io::gpio::{
    ClockNature, Edge, GpioPin, MonitoringReadResponse, MonitoringStartResponse, PinMode, PullMode,
};
use opentitanlib::transport::Capability;
use opentitanlib::util::file;
use opentitanlib::util::raw_tty::RawTty;
use opentitanlib::util::voltage::Voltage;

#[derive(Debug, Args)]
/// Reads a GPIO pin.
pub struct GpioRead {
    /// The GPIO pin to read.
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
    /// The GPIO pin to write.
    pub pin: String,
    /// The value to write to the pin.
    #[arg(action = clap::ArgAction::Set)]
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
    /// The GPIO pin to modify.
    pub pin: String,
    /// The I/O mode of the pin.
    #[arg(value_enum, ignore_case = true)]
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
    /// The GPIO pin to modify.
    pub pin: String,
    /// The weak pull mode of the pin.
    #[arg(value_name = "PULLMODE", value_enum, ignore_case = true)]
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
    /// The GPIO pin to modify.
    pub pin: String,
    /// The I/O mode of the pin.
    #[arg(long, ignore_case = true)]
    pub mode: Option<PinMode>,
    /// The value to write to the pin, has effect only in PushPull and OpenDrain modes.
    #[arg(long, value_parser = bool::from_str)]
    pub value: Option<bool>,
    /// The weak pull mode of the pin.
    #[arg(long, ignore_case = true)]
    pub pull: Option<PullMode>,
    /// The analog value to write to the pin in volts, has effect only in AnalogOutput mode.
    #[arg(long)]
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
    /// The GPIO pin to read.
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
    /// The GPIO pin to write.
    pub pin: String,
    /// The analog value to write to the pin in volts, has effect only in AnalogOutput mode.
    pub voltage: Voltage,
}

impl CommandDispatch for GpioAnalogWrite {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport.capabilities()?.request(Capability::GPIO).ok()?;
        let gpio_pin = transport.gpio_pin(&self.pin)?;

        gpio_pin.analog_write(self.voltage.as_volts() as f32)?;
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Apply a configuration-named pin strapping
pub struct GpioApplyStrapping {
    /// The pin strapping to apply.
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
    /// The list of GPIO pins to monitor (space separated).
    pub pins: Vec<String>,

    /// Location of optional output file to record the vcd header information.
    #[arg(short, long)]
    pub outfile: Option<String>,
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

        // If vcd output file was was provided, record results there.
        if let Some(file) = &self.outfile {
            write_vcd_header(file, &self.pins, clock_nature, &resp)?;
        }

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
    /// The list of GPIO pins being monitored (space separated).
    pub pins: Vec<String>,

    #[arg(long)]
    pub continue_monitoring: bool,

    /// Optional vcd file to append data to. Note it is important that the gpios are in the same
    /// order from the gpio start command where the vcd header was written.
    #[arg(short, long)]
    outfile: Option<String>,
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
        // If vcd output file was specified, write data there.
        if let Some(file) = &self.outfile {
            append_vcd_data(file, &resp, !self.continue_monitoring)?;
        }
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

/// Write the VCD header data with the given inputs
fn write_vcd_header(
    file: &str,
    pins: &[String],
    clock_nature: ClockNature,
    start_response: &MonitoringStartResponse,
) -> Result<()> {
    let mut file = File::create(file)?;
    writeln!(&mut file, "$version")?;
    let version = super::version::VersionResponse::default();
    writeln!(
        &mut file,
        "   opentitantool {} {}",
        version.version.as_ref().map_or("<unknown>", String::as_str),
        match version.clean {
            Some(true) => "clean",
            Some(false) => "modified",
            None => "<unknown>",
        }
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
    for (n, pin) in pins.iter().enumerate() {
        writeln!(&mut file, "$var wire 1 '{} {} $end", n, pin)?;
    }
    writeln!(&mut file, "$upscope $end")?;
    writeln!(&mut file, "$enddefinitions $end")?;
    writeln!(&mut file, "#{}", start_response.timestamp)?;
    for (n, v) in start_response.initial_levels.iter().enumerate() {
        writeln!(&mut file, "{}'{}", if *v { 1 } else { 0 }, n)?;
    }
    Ok(())
}

/// Appends the VCD data to the end of the file specified. Note the order of the gpios should
/// be consistent between calls and match the order from the gpio start command.
fn append_vcd_data(file: &str, read_response: &MonitoringReadResponse, last: bool) -> Result<()> {
    let mut file = std::fs::OpenOptions::new().append(true).open(file)?;
    for event in &read_response.events {
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
    if last {
        writeln!(&mut file, "#{}", read_response.timestamp)?;
    }
    Ok(())
}

#[derive(Debug, Args)]
/// Whereas `monitoring start` and `monitoring read` are meant for use by scripts, this
/// `monitoring vcd` is intended for manual use by an operator.  It will stay in the foreground,
/// collecting events until the user presses Ctrl-C.  A transcript will be written in the industry
/// standard VCD format, which can be loaded into e.g. Pulseview (or probably also Saleae
/// software), to get a logic analyzer view of what transpired.
pub struct GpioMonitoringVcd {
    /// The list of GPIO pins to monitor (space separated).
    pub pins: Vec<String>,

    /// Output file.
    #[arg(short, long)]
    outfile: String,

    /// Do not print start end exit messages.
    #[arg(short, long)]
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

        if !self.quiet {
            eprintln!("Dumping events to {}", &self.outfile);
            eprint!("[CTRL+C] to exit  ");
        }
        // Putting the terminal input into raw mode is the only way we can catch Ctrl-C.  (This is
        // not ideal, it would have been better to catch the SIGINT signal, but the mio_signals
        // package is not compatible with the way that our rusb library uses background threads.)
        // The tty guard will restore the console settings when it goes out of scope.
        let mut stdin = RawTty::new(std::io::stdin())?;

        // Inform the transport that we want to monitor a set of pins, and write a file header
        // with the names of each of the monitored signals.
        let initial = gpio_monitoring.monitoring_start(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
        )?;

        let clock_nature = gpio_monitoring.get_clock_nature()?;
        write_vcd_header(&self.outfile, &self.pins, clock_nature, &initial)?;

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
            append_vcd_data(&self.outfile, &resp, false)?;
            eprint!("\u{8}{}", ['/', '-', '\\', '|'][loop_count & 3usize]);
            let delay = if resp.events.is_empty() {
                Duration::from_millis(10)
            } else {
                Duration::from_millis(0)
            };
            if file::wait_read_timeout(&stdin, delay).is_ok() {
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
        append_vcd_data(&self.outfile, &resp, true)?;
        eprintln!("\r");
        Ok(None)
    }
}

#[derive(Debug, Args)]
/// Remove a configuration-named pin strapping
pub struct GpioRemoveStrapping {
    /// The pin strapping to release.
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

#[derive(Debug, Args)]
/// Manipulates a given set of GPIO pins, clocking out successive samples at a given frequency.
pub struct GpioBitbang {
    /// The list of GPIO pins to manipulate (space separated).
    pub pins: Vec<String>,

    #[arg(long, value_parser = opentitanlib::util::bitbang::parse_clock_frequency)]
    pub clock: Duration,

    #[arg(short, long)]
    pub sequence: String,

    #[arg(short, long)]
    pub all: bool,
}

#[derive(serde::Serialize)]
pub struct GpioBitbangResult {
    /// Samples of input, gathered at particular times while the waveform was generated, according
    /// to instructions in the `sequence` argument.
    samples: HashMap<String, String>,

    /// Transcript of logic levels of all affected pins at each clock tick.  Only populated if
    /// `--all` was requested.
    all: Vec<String>,
}

/// Composes a string of '0' and '1', with the least significant bit first in the string (opposite
/// of ordinary numbers).  This is used to print logic levels of the set of pins listed on the
/// command line.
fn binary_string(data: u8, num_digits: usize) -> String {
    let mut val = String::new();
    for i in 0..num_digits {
        val += if data & (1 << i) != 0 { "1" } else { "0" };
    }
    val
}

impl CommandDispatch for GpioBitbang {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport
            .capabilities()?
            .request(Capability::GPIO_BITBANGING)
            .ok()?;
        let gpio_bitbanging = transport.gpio_bitbanging()?;
        let gpio_pins = transport.gpio_pins(&self.pins)?;
        let mut outbound_data_accumulator: Vec<u8> = Vec::new();
        let mut inbound_data_accumulator: Vec<u8> = Vec::new();
        let (sequence, output_map) = opentitanlib::util::bitbang::parse_sequence(
            &self.sequence,
            gpio_pins.len(),
            self.clock,
            &mut inbound_data_accumulator,
            &mut outbound_data_accumulator,
        )?;
        gpio_bitbanging.run(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
            self.clock,
            sequence,
        )?;
        let mut samples = HashMap::new();
        for (label, byte_index) in output_map {
            let sampled_data = inbound_data_accumulator[byte_index];
            samples.insert(
                label.to_string(),
                binary_string(sampled_data, gpio_pins.len()),
            );
        }
        let mut all = Vec::new();
        if self.all {
            for sampled_data in inbound_data_accumulator {
                all.push(binary_string(sampled_data, gpio_pins.len()));
            }
        }
        Ok(Some(Box::new(GpioBitbangResult { samples, all })))
    }
}

#[derive(Debug, Args)]
/// Manipulates a given set of analog output pins, clocking out successive samples at a given
/// frequency.
pub struct GpioDacBang {
    /// The list of analog output pins to manipulate (space separated).
    pub pins: Vec<String>,

    #[arg(long, value_parser = opentitanlib::util::bitbang::parse_clock_frequency)]
    pub clock: Duration,

    #[arg(short, long)]
    pub sequence: String,
}

impl CommandDispatch for GpioDacBang {
    fn run(
        &self,
        _context: &dyn Any,
        transport: &TransportWrapper,
    ) -> Result<Option<Box<dyn Annotate>>> {
        transport
            .capabilities()?
            .request(Capability::GPIO_BITBANGING)
            .ok()?;
        let gpio_bitbanging = transport.gpio_bitbanging()?;
        let gpio_pins = transport.gpio_pins(&self.pins)?;
        let mut data_accumulator: Vec<f32> = Vec::new();
        let sequence = opentitanlib::util::bitbang::parse_dac_sequence(
            &self.sequence,
            gpio_pins.len(),
            self.clock,
            &mut data_accumulator,
        )?;
        gpio_bitbanging.dac_run(
            &gpio_pins
                .iter()
                .map(Rc::borrow)
                .collect::<Vec<&dyn GpioPin>>(),
            self.clock,
            sequence,
        )?;
        Ok(None)
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
    Bitbang(GpioBitbang),
    DacBang(GpioDacBang),
}
