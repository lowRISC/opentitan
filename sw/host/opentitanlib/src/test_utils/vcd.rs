// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::time::Duration;
use thiserror::Error;

use crate::impl_serializable_error;

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

/// Dump a single discrete waveform sample as a VCD value change based on the
/// previous sample, which will be updated with the provided sample.
fn dump_vcd_sample(
    pin_vars: &[char],
    timestamp: u64,
    previous: &mut Option<u8>,
    sample: u8,
) -> Result<Option<String>> {
    let num_pins = pin_vars.len();
    ensure!(
        (1..=7).contains(&num_pins),
        VcdError::UnsupportedVariableCount(num_pins)
    );

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
fn dump_vcd_vardefs(vars: &[char], pin_names: &[Option<String>]) -> Result<String> {
    let num_pins = pin_names.len();
    ensure!(
        (1..=7).contains(&num_pins),
        VcdError::UnsupportedVariableCount(num_pins)
    );
    let mut vcd = String::new();
    vcd.push_str("$scope module opentitanlib $end\n");
    for (i, pin) in pin_names.iter().enumerate() {
        let pin_name = pin.clone().unwrap_or(format!("pin_{}", i));
        vcd.push_str(&format!("$var wire 1 {} {} $end\n", vars[i], pin_name,));
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
    let vars: &[char] = &(33u8..(33 + pin_names.len() as u8))
        .map(|c| c as char)
        .collect::<Vec<_>>();
    let mut vcd = dump_vcd_header(clock_tick);
    vcd.push_str(&dump_vcd_vardefs(vars, pin_names)?);
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

#[cfg(test)]
mod test {
    use super::*;

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
}
