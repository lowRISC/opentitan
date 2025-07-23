// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::time::Duration;
use thiserror::Error;

use crate::impl_serializable_error;
use crate::io::gpio::{Edge, MonitoringEvent, MonitoringReadResponse};

/// Errors related to VCD encoding/decoding
#[derive(Debug, Error, Serialize, Deserialize)]
pub enum VcdError {
    #[error("Missing required {0} value")]
    MissingValue(String),
    #[error("Missing required definition {0}")]
    MissingDefinition(String),
    #[error("Missing $end for definition {0}")]
    MissingDefinitionEnd(String),
    #[error("Multiple definitions for {0}")]
    MultipleDefinitions(String),
    #[error("Found $end when there was no definition to end")]
    MismatchedEnd,
    #[error("Found a $scope after already parsing $enddefinitions")]
    DefinitionAfterEnd,
    #[error("VCD parsing currently only supports <= 8 variables")]
    UnsupportedVariableCount(usize),
    #[error("{0} is not yet supported by VCD parsing")]
    UnsupportedFeature(String),
    #[error("VCD timestamps #{0} and #{1} are out of order!")]
    TimestampsOutOfOrder(u64, u64),
    #[error("Unrecognized value {0}")]
    UnknownToken(String),
    #[error("Supplied identifier {0} does not match any defined identifier")]
    UnknownVariable(String),
}
impl_serializable_error!(VcdError);

/// Convert a `u64` timestamp from the GpioMonitoring interface to a time in
/// nanoseconds given some initial timestamp measurement and a clock resolution.
fn timestamp_to_nanos(initial: u64, timestamp: u64, clock_res: u64) -> u64 {
    let delta = (timestamp - initial) as u128;
    let nanos = delta * 1_000_000_000u128 / clock_res as u128;
    nanos as u64
}

/// Convert a time in nanoseconds to a timestamp used with the GpioMonitoring
/// interface, using some initial timestamp measurement & a clock resolution.
fn timestamp_from_nanos(initial: u64, nanos: u64, clock_res: u64) -> u64 {
    let delta = (nanos as u128) * (clock_res as u128) / 1_000_000_000u128;
    initial + delta as u64
}

/// Dump a single discrete waveform sample as a VCD value change based on the
/// previous sample, which will be updated with the provided sample.
fn dump_vcd_sample(
    pin_vars: &[String],
    timestamp: u64,
    previous: &mut Option<u8>,
    sample: u8,
) -> Result<Option<String>> {
    let num_pins = pin_vars.len();

    // Calculate any changes from the previous sample
    let mut bits = Vec::with_capacity(8);
    for i in 0..num_pins {
        let bit = (sample >> i) & 0x01;
        let prev_bit = previous.map(|s| (s >> i) & 0x01);
        if prev_bit.is_none() || prev_bit.unwrap() != bit {
            bits.push((i, bit));
        }
    }

    // Write all the value changes for this timestamp
    *previous = Some(sample);
    if bits.is_empty() {
        return Ok(None);
    }
    let mut vcd = String::new();
    vcd.push_str(&format!("#{}", timestamp));
    for (i, bit) in bits {
        ensure!(i < num_pins, VcdError::UnsupportedVariableCount(num_pins));
        vcd.push_str(&format!(" {}{}", bit, pin_vars[i]));
    }
    vcd.push('\n');
    Ok(Some(vcd))
}

/// Dump the VCD header for a given waveform, which just stores info about the
/// `clock_tick` (bitbanging period).
fn dump_vcd_header(clock_tick: Duration) -> String {
    format!("$timescale {}ns $end\n", clock_tick.as_nanos())
}

/// Dump the VCD variable definitions for a given waveform. All variables are
/// written in order, with the provided names, under the single scope
/// `opentitanlib`. Unspecified names default to e.g. `pin_X`.
fn dump_vcd_vardefs(pins: &[(&String, &Option<String>)]) -> Result<String> {
    let mut vcd = String::new();
    vcd.push_str("$scope module opentitanlib $end\n");
    for (i, (var, pin)) in pins.iter().enumerate() {
        let pin_name = pin.as_ref().map_or(format!("pin_{}", i), |n| n.clone());
        vcd.push_str(&format!("$var wire 1 {} {} $end\n", var, pin_name));
    }
    vcd.push_str("$upscope $end\n");
    vcd.push_str("$enddefinitions $end\n");
    Ok(vcd)
}

/// Dump a VCD of a uniformly (discretely) sampled waveform, represented by
/// a list of bytes (pin values over time) and a `clock_tick` (sampling period).
/// Variables are defined in order corresponding to LSBs in the sample.
pub fn dump_vcd_from_samples(
    pin_names: &[Option<String>],
    clock_tick: Duration,
    samples: &[u8],
) -> Result<String> {
    let vars = &(0..pin_names.len())
        .map(|c| format!("'{}", c))
        .collect::<Vec<_>>();
    let mut vcd = dump_vcd_header(clock_tick);
    let pins = vars.iter().zip(pin_names).collect::<Vec<_>>();
    vcd.push_str(&dump_vcd_vardefs(&pins)?);
    let mut prev_sample = None;
    let mut last_sample_index = 0;
    for (i, sample) in samples.iter().enumerate() {
        if let Some(sample) = dump_vcd_sample(vars, i as u64, &mut prev_sample, *sample)? {
            vcd.push_str(&sample);
            last_sample_index = i;
        }
    }
    // Make sure we include an ending timestamp for the final sample
    if (last_sample_index + 1) < samples.len() {
        vcd.push_str(&format!("\n#{}", samples.len() - 1));
    }
    vcd.push('\n');
    Ok(vcd)
}

/// Dump a VCD of a waveform represented by a chronological sequence of rising /
/// falling edges (i.e. value changes) as is returned by the `GpioMonitoring`
/// interface. This includes an initial & final timestamp, some initial values,
/// and a list of edge `events`.
pub fn dump_vcd_from_edges(
    pin_names: &[Option<String>],
    clock_resolution: u64,
    initial_timestamp: u64,
    initial_values: &[bool],
    events: &[MonitoringEvent],
    final_timestamp: u64,
) -> Result<String> {
    let vars = &(0..pin_names.len())
        .map(|c| format!("'{}", c))
        .collect::<Vec<_>>();
    let mut vcd = dump_vcd_header(Duration::from_nanos(1));
    let pins = vars.iter().zip(pin_names).collect::<Vec<_>>();
    vcd.push_str(&dump_vcd_vardefs(&pins)?);
    // Dump the initial values
    vcd.push_str("#0");
    for (&bit, var) in initial_values.iter().zip(vars.iter()) {
        vcd.push_str(&format!(" {}{}", bit as u8, var));
    }
    // Edge events are essentially 1-to-1 with the VCD format
    let mut timestamp: u64 = 0;
    for event in events.iter() {
        let edge_time = timestamp_to_nanos(initial_timestamp, event.timestamp, clock_resolution);
        if edge_time > timestamp {
            timestamp = edge_time;
            vcd.push_str(&format!("\n#{}", edge_time));
        }
        let index = event.signal_index as usize;
        let bit = if event.edge == Edge::Rising { 1 } else { 0 };
        vcd.push_str(&format!(" {}{}", bit, vars[index]));
    }
    // Include a final timestamp marking the final measurement
    let end_time = timestamp_to_nanos(initial_timestamp, final_timestamp, clock_resolution);
    vcd.push_str(&format!("\n#{}\n", end_time));
    Ok(vcd)
}

/// Parse a `$timescale` definition in a VCD header, returning the timescale as
/// a duration. Expects to be used after consuming a `$timescale` token.
fn parse_vcd_header_timescale<'a>(vcd: &mut impl Iterator<Item = &'a str>) -> Result<Duration> {
    let Some(timescale) = vcd.next() else {
        return Err(VcdError::MissingValue("timescale".into()).into());
    };
    let clock_tick = humantime::parse_duration(timescale)?;
    match vcd.next() {
        Some("$end") => Ok(clock_tick),
        _ => Err(VcdError::MissingDefinitionEnd("timescale".into()).into()),
    }
}

/// Parse a VCD header, returning the parsed timescale as a duration. Expects
/// no previous tokens to have been consumed.
fn parse_vcd_header<'a>(vcd: &mut impl Iterator<Item = &'a str>) -> Result<Duration> {
    let mut timescale = None;
    #[allow(clippy::while_let_on_iterator)]
    while let Some(token) = vcd.next() {
        match token {
            "$timescale" => {
                if timescale.is_some() {
                    return Err(VcdError::MultipleDefinitions("timescale".into()).into());
                }
                timescale = Some(parse_vcd_header_timescale(vcd)?)
            }
            "$scope" => {
                return if let Some(clock_tick) = timescale {
                    Ok(clock_tick)
                } else {
                    Err(VcdError::MissingDefinition("timescale".into()).into())
                };
            }
            _ => (),
        }
    }
    Err(VcdError::MissingDefinition("scope".into()).into())
}

/// Parse a `$var` definition in a VCD's variable definition section, returning
/// the parsed identifier. Expects to be used after consuming a `$var` token.
fn parse_vcd_variable<'a>(vcd: &mut impl Iterator<Item = &'a str>) -> Result<&'a str> {
    let Some(_var_type) = vcd.next() else {
        return Err(VcdError::MissingValue("var type".into()).into());
    };
    let Some(var_size) = vcd.next() else {
        return Err(VcdError::MissingValue("var type".into()).into());
    };
    let var_size = var_size.parse::<usize>()?;
    if var_size != 1 {
        return Err(VcdError::UnsupportedFeature("vector signals".into()).into());
    }
    let Some(identifier) = vcd.next() else {
        return Err(VcdError::MissingValue("identifier".into()).into());
    };
    let Some(_var_name) = vcd.next() else {
        return Err(VcdError::MissingValue("var name".into()).into());
    };
    match vcd.next() {
        Some("$end") => Ok(identifier),
        _ => Err(VcdError::MissingDefinitionEnd("var".into()).into()),
    }
}

/// Parse a `$scope` definition in a VCD's variable definition section. Pushes
/// the identifiers of parsed variables within the scope (and any sub-scopes) to
/// an `identifiers` Vec. Expects to be used after consuming a `$scope` token.
fn parse_vcd_scope<'a>(
    path: &str,
    identifiers: &mut Vec<String>,
    vcd: &mut impl Iterator<Item = &'a str>,
) -> Result<()> {
    if vcd.next().is_none() {
        return Err(VcdError::MissingValue("scope type".into()).into());
    };
    let Some(scope_name) = vcd.next() else {
        return Err(VcdError::MissingValue("scope name".into()).into());
    };
    match vcd.next() {
        Some("$end") => (),
        _ => return Err(VcdError::MissingDefinitionEnd("scope".into()).into()),
    };
    let next_path = format!("{}.{}", path, scope_name);
    #[allow(clippy::while_let_on_iterator)]
    while let Some(token) = vcd.next() {
        match token {
            "$scope" => parse_vcd_scope(&next_path, identifiers, vcd)?,
            "$var" => {
                let identifier = parse_vcd_variable(vcd)?;
                identifiers.push(identifier.to_string());
            }
            "$end" => return Ok(()),
            _ => (),
        }
    }
    Err(VcdError::MissingDefinitionEnd("scope".into()).into())
}

/// Parse a VCD's variable definitions section, returning a vector of all the
/// parsed variable identifiers. Expects the `$scope` token marking the start
/// of the section to have already been consumed.
fn parse_vcd_vardefs<'a>(vcd: &mut impl Iterator<Item = &'a str>) -> Result<Vec<String>> {
    let mut identifiers = Vec::new();
    parse_vcd_scope("", &mut identifiers, vcd)?;
    let mut end_seen = false;
    #[allow(clippy::while_let_on_iterator)]
    while let Some(token) = vcd.next() {
        match (token, end_seen) {
            ("$scope", false) => {
                parse_vcd_scope("", &mut identifiers, vcd)?;
            }
            ("$scope", true) => return Err(VcdError::DefinitionAfterEnd.into()),
            ("$enddefinitions", false) => {
                end_seen = true;
            }
            ("$enddefinitions", true) => {
                return Err(VcdError::MultipleDefinitions("$enddefinitions".into()).into())
            }
            ("$end", false) => return Err(VcdError::MismatchedEnd.into()),
            ("$end", true) => return Ok(identifiers),
            _ => (),
        }
    }
    Err(VcdError::MissingDefinition("$enddefinitions".into()).into())
}

/// Parse a scalar value from the value change section of a VCD value. Given a
/// list of identifiers e.g. ["$", "#", ":"] and some value e.g. "1#" or "0$"
/// this will find & return the matching identifier index.
fn parse_vcd_scalar(identifiers: &[String], value: &str) -> Result<usize> {
    let ident = &value[1..];
    if let Some(index) = identifiers.iter().position(|id| id == ident) {
        Ok(index)
    } else {
        Err(VcdError::UnknownVariable(ident.into()).into())
    }
}

/// Parse the value change section of a VCD to a list of samples representing
/// the shape of the uniformly (discretely) sampled waveform. Expects to be
/// used after the `$end` token has been consumed but before any variable change
/// tokens have been seen.
fn parse_vcd_values_to_samples<'a>(
    identifiers: &[String],
    vcd: &mut impl Iterator<Item = &'a str>,
) -> Result<Vec<u8>> {
    let mut samples = Vec::new();
    let mut current_time: usize = 0;
    let mut current_values: u8 = 0x00;
    #[allow(clippy::while_let_on_iterator)]
    while let Some(token) = vcd.next() {
        match token {
            // Commands
            "$dumpvars" => return Err(VcdError::UnsupportedFeature("$dumpvars".into()).into()),
            "$end" => return Err(VcdError::MismatchedEnd.into()),
            v if v.starts_with("$") => {
                return Err(VcdError::UnsupportedFeature("commands".into()).into())
            }
            // Timesteps
            v if v.starts_with("#") => {
                let value = v.strip_prefix("#").unwrap().parse::<usize>()?;
                match value.cmp(&current_time) {
                    Ordering::Less => {
                        return Err(VcdError::TimestampsOutOfOrder(
                            current_time as u64,
                            value as u64,
                        )
                        .into())
                    }
                    Ordering::Greater => {
                        for _ in current_time..value {
                            samples.push(current_values);
                        }
                        current_time = value;
                    }
                    Ordering::Equal => (),
                }
            }
            // Values
            v if v.starts_with("0") || v.starts_with("1") => {
                let value = if v.starts_with("0") { 0 } else { 1 };
                let index = parse_vcd_scalar(identifiers, v)?;
                current_values &= !(1 << index);
                current_values |= value << index;
            }
            v if v.starts_with("z")
                || v.starts_with("Z")
                || v.starts_with("x")
                || v.starts_with("X") =>
            {
                return Err(VcdError::UnsupportedFeature("non-binary scalars".into()).into())
            }
            v if v.starts_with("b") || v.starts_with("B") => {
                return Err(VcdError::UnsupportedFeature("vector signals".into()).into())
            }
            v if v.starts_with("r") || v.starts_with("R") => {
                return Err(VcdError::UnsupportedFeature("real vars".into()).into())
            }
            v if v.starts_with("s") || v.starts_with("S") => {
                return Err(VcdError::UnsupportedFeature("strings".into()).into())
            }
            v => return Err(VcdError::UnknownToken(v.into()).into()),
        }
    }
    samples.push(current_values);
    Ok(samples)
}

/// Parse the value change section of a VCD to a list of `MonitoringEvent`s, each
/// of which corresponds to an edge on some signal (a value change). Expects to
/// be used after the `$end` token has been consumed but before any variable
/// change tokens have been seen.
/// A clock resolution and initial timestamp can be provided to scale/offsetthe
/// timesteps being used from the default of 1ns & 0.
fn parse_vcd_values_to_edges<'a>(
    identifiers: &[String],
    timescale: Duration,
    clock_resolution: u64,
    initial_timestamp: u64,
    vcd: &mut impl Iterator<Item = &'a str>,
) -> Result<(u64, Vec<MonitoringEvent>)> {
    let timescale = timescale.as_nanos() as u64;
    let mut events = Vec::new();
    let mut current_time: u64 = 0;
    let mut current_values: u8 = 0x00;
    #[allow(clippy::while_let_on_iterator)]
    while let Some(token) = vcd.next() {
        match token {
            // Commands
            "$dumpvars" => return Err(VcdError::UnsupportedFeature("$dumpvars".into()).into()),
            "$end" => return Err(VcdError::MismatchedEnd.into()),
            v if v.starts_with("$") => {
                return Err(VcdError::UnsupportedFeature("commands".into()).into())
            }
            // Timesteps
            v if v.starts_with("#") => {
                let value = v.strip_prefix("#").unwrap().parse::<u64>()?;
                if value < current_time {
                    return Err(VcdError::TimestampsOutOfOrder(current_time, value).into());
                }
                current_time = value;
            }
            // Values
            v if v.starts_with("0") || v.starts_with("1") => {
                let value = if v.starts_with("0") { 0 } else { 1 };
                let index = parse_vcd_scalar(identifiers, v)?;
                let current_value = current_values >> index & 0x01;
                if value != current_value {
                    current_values &= !(1 << index);
                    current_values |= value << index;
                    // Don't generate edges for initial signal values.
                    if current_time == 0 {
                        // TODO: maybe this should be parsed from a `$dumpvars`
                        // and not `#0`, as we might have an edge at `t=0`?
                        continue;
                    }
                    let nanos = current_time.div_ceil(timescale);
                    let timestamp =
                        timestamp_from_nanos(initial_timestamp, nanos, clock_resolution);
                    events.push(MonitoringEvent {
                        signal_index: index as u8,
                        edge: if value == 1 {
                            Edge::Rising
                        } else {
                            Edge::Falling
                        },
                        timestamp,
                    });
                }
            }
            v if v.starts_with("z")
                || v.starts_with("Z")
                || v.starts_with("x")
                || v.starts_with("X") =>
            {
                return Err(VcdError::UnsupportedFeature("non-binary scalars".into()).into())
            }
            v if v.starts_with("b") || v.starts_with("B") => {
                return Err(VcdError::UnsupportedFeature("vector signals".into()).into())
            }
            v if v.starts_with("r") || v.starts_with("R") => {
                return Err(VcdError::UnsupportedFeature("real vars".into()).into())
            }
            v if v.starts_with("s") || v.starts_with("S") => {
                return Err(VcdError::UnsupportedFeature("strings".into()).into())
            }
            v => return Err(VcdError::UnknownToken(v.into()).into()),
        }
    }
    // Determine a final timestamp for the waveform from the last timestep seen
    let last_nanos = current_time.div_ceil(timescale);
    let last_timestamp = timestamp_from_nanos(initial_timestamp, last_nanos, clock_resolution);
    Ok((last_timestamp, events))
}

/// Lexes the VCD, returning an iterator over all whitespace-separated tokens.
fn tokenize_vcd(vcd: &str) -> impl Iterator<Item = &str> {
    vcd.lines().flat_map(|line| line.split_whitespace())
}

/// The output of parsing a VCD to a Vec of discrete samples, including the
/// samples itself, as well as any parsed pin variables and the timescale.
pub struct ParsedVcdSamples {
    pub pin_vars: Vec<String>,
    pub clock_tick: Duration,
    pub samples: Vec<u8>,
}

/// Parses a VCD (given its contents) to a Vec of discrete samples, with
/// one sample per configured timescale (`clock_tick`).
pub fn parse_vcd_to_samples(vcd: &str) -> Result<ParsedVcdSamples> {
    let mut tokens = tokenize_vcd(vcd);
    let clock_tick = parse_vcd_header(&mut tokens)?;
    let pin_vars = parse_vcd_vardefs(&mut tokens)?;
    ensure!(
        pin_vars.len() < 8,
        VcdError::UnsupportedVariableCount(pin_vars.len())
    );
    let samples = parse_vcd_values_to_samples(&pin_vars, &mut tokens)?;
    Ok(ParsedVcdSamples {
        pin_vars,
        clock_tick,
        samples,
    })
}

/// The output of parsing a VCD to a Vec of discrete samples, including the
/// samples itself, as well as any parsed pin variables and the timescale.
/// The output of parsing a VCD to a Vec of edges, including the edges as a
/// `MonitoringReadResponse` and any parsed pin variables.
pub struct ParsedVcdEdges {
    pub pin_vars: Vec<String>,
    pub events: MonitoringReadResponse,
}

/// Parses a VCD (given its contents) to a Vec of edges (value changes), with
/// timestamps relative to the `clock_resolution` and `initial_timestamp`.
pub fn parse_vcd_to_edges(
    vcd: &str,
    clock_resolution: u64,
    initial_timestamp: u64,
) -> Result<ParsedVcdEdges> {
    let mut tokens = tokenize_vcd(vcd);
    let clock_tick = parse_vcd_header(&mut tokens)?;
    let pin_vars = parse_vcd_vardefs(&mut tokens)?;
    ensure!(
        pin_vars.len() < 8,
        VcdError::UnsupportedVariableCount(pin_vars.len())
    );
    let (timestamp, events) = parse_vcd_values_to_edges(
        &pin_vars,
        clock_tick,
        clock_resolution,
        initial_timestamp,
        &mut tokens,
    )?;
    let events = MonitoringReadResponse { events, timestamp };
    Ok(ParsedVcdEdges { pin_vars, events })
}

#[cfg(test)]
mod test {
    use super::*;

    // A helper to compactly construct `MonitoringEvent` edges.
    fn edge(signal_index: u8, edge: Edge, timestamp: u64) -> MonitoringEvent {
        MonitoringEvent {
            signal_index,
            edge,
            timestamp,
        }
    }

    // Test by dumping a given uniformly sampled waveform to a VCD and parsing
    // it back, to check the decoded contents match the original.
    fn samples_encode_decode(
        samples: &[u8],
        pin_names: &[Option<String>],
        clock_tick: Duration,
    ) -> Result<()> {
        let vcd = dump_vcd_from_samples(pin_names, clock_tick, samples)?;
        assert!(!vcd.is_empty());
        // For now this test assumes the order of bits is retained (i.e. vars
        // are parsed into sample bit indexes in the same order they are defined).
        let decoded = parse_vcd_to_samples(&vcd)?;
        assert_eq!(&decoded.samples, samples);
        Ok(())
    }

    // Test by dumping a given edge-represented waveform to a VCD and parsing it
    // back, to check the decoded contents match the original.
    fn edges_encode_decode(
        clock_resolution: u64,
        initial_timestamp: u64,
        initial_values: &[bool],
        events: &[MonitoringEvent],
        final_timestamp: u64,
        pin_names: &[Option<String>],
    ) -> Result<()> {
        let vcd = dump_vcd_from_edges(
            pin_names,
            clock_resolution,
            initial_timestamp,
            initial_values,
            events,
            final_timestamp,
        )?;
        assert!(!vcd.is_empty());
        // For now this test assumes the order of signals is retained (i.e.
        // vars are parsed into signal indexes in the order they are defined).
        let decoded = parse_vcd_to_edges(&vcd, clock_resolution, initial_timestamp)?;
        assert_eq!(decoded.events.timestamp, final_timestamp);
        assert_eq!(decoded.events.events, events);
        Ok(())
    }

    #[test]
    fn samples_waveform() -> Result<()> {
        // Random waveform over 3 pins, with a clock_tick of 3 us.
        let samples = [
            4, 5, 3, 4, 1, 3, 6, 0, 2, 4, 5, 1, 7, 2, 3, 4, 0, 0, 1, 4, 0, 1, 2, 3, 4, 6,
        ];
        let pin_names = [const { None }; 3];
        let clock_tick = Duration::from_nanos(3000);
        samples_encode_decode(&samples, &pin_names, clock_tick)?;

        // Example SPI waveform over 3 pins, again with a clock_tick of 3 us.
        let pin_names = [
            Some("spi_sck".into()),
            Some("spi_cs".into()),
            Some("spi_copi".into()),
        ];
        let samples = [
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 4,
            5, 4, 5, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
            0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
            1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
            0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
            1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
            0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
            1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
            0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
            1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
            2,
        ];
        samples_encode_decode(&samples, &pin_names, clock_tick)
    }

    #[test]
    fn edges_waveform() -> Result<()> {
        // Random waveform over 3 pins, with a clock_tick of 1 us.
        let clock_resolution = 1_000_000; // Each clock tick is 1 us.
        let initial_timestamp = 536;
        let initial_values = vec![true, false, true];
        let events = Vec::from([
            edge(2, Edge::Falling, 562),
            edge(1, Edge::Rising, 621),
            edge(0, Edge::Falling, 754),
            edge(2, Edge::Rising, 832),
            edge(2, Edge::Falling, 855),
            edge(2, Edge::Rising, 912),
            edge(0, Edge::Rising, 1012),
            edge(1, Edge::Falling, 1058),
            edge(2, Edge::Falling, 1123),
            edge(2, Edge::Rising, 1157),
            edge(0, Edge::Falling, 1210),
            edge(1, Edge::Rising, 1258),
            edge(0, Edge::Rising, 1315),
            edge(2, Edge::Falling, 1415),
            edge(1, Edge::Falling, 1510),
            edge(0, Edge::Falling, 1633),
            edge(0, Edge::Rising, 1901),
        ]);
        let final_timestamp = 1947;
        let pin_names = [const { None }; 3];
        edges_encode_decode(
            clock_resolution,
            initial_timestamp,
            &initial_values,
            &events,
            final_timestamp,
            &pin_names,
        )?;

        // Example UART RX waveform with 1 pin taken from a bitbanging test sample
        let initial_timestamp = 0;
        let initial_values = vec![true];
        let event_timestamps = [
            5889252340, 5889252358, 5889252375, 5889252392, 5889252410, 5889252427, 5889252445,
            5889252462, 5889252479, 5889252497, 5889252514, 5889252532, 5889252549, 5889252636,
            5889252654, 5889252671, 5889252688, 5889252723, 5889252740, 5889252775, 5889252793,
            5889252810, 5889252827, 5889252845, 5889252862, 5889252914, 5889252932, 5889252949,
            5889252967, 5889252984, 5889253001, 5889253019, 5889253036, 5889253141, 5889253158,
            5889253193, 5889253210, 5889253245, 5889253263, 5889253315, 5889253349, 5889253367,
            5889253386, 5889253402, 5889253419, 5889253454, 5889253471, 5889253489, 5889253523,
            5889253541, 5889253558, 5889253610, 5889253628, 5889253645, 5889253697, 5889253715,
            5889253732, 5889253767, 5889253784, 5889253837, 5889253871, 5889253889, 5889253906,
            5889253924, 5889253941, 5889254011, 5889254046, 5889254063, 5889254080, 5889254115,
            5889254167, 5889254185, 5889254219, 5889254238, 5889254254, 5889254272, 5889254324,
            5889254359, 5889254393, 5889254411, 5889254428, 5889254533, 5889254550, 5889254585,
            5889254603, 5889254655, 5889254672, 5889254689, 5889254741, 5889254759, 5889254776,
            5889254794, 5889254811, 5889254828, 5889254846, 5889254881, 5889254915, 5889254933,
            5889254950, 5889254968, 5889255002, 5889255037, 5889255089, 5889255107, 5889255124,
            5889255176, 5889255194, 5889255211, 5889255264, 5889255281, 5889255298, 5889255455,
        ];
        let edges = [Edge::Falling, Edge::Rising];
        let events = event_timestamps
            .into_iter()
            .enumerate()
            .map(|(i, t)| edge(0, edges[i % 2], t))
            .collect::<Vec<_>>();
        let final_timestamp = 5889262827;
        let pin_names = [Some("uart_rx".into())];
        edges_encode_decode(
            clock_resolution,
            initial_timestamp,
            &initial_values,
            &events,
            final_timestamp,
            &pin_names,
        )
    }
}
