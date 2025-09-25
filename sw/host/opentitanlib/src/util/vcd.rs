// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, bail};
use std::io;
use thiserror::Error;

use crate::io::gpio::{Edge, MonitoringEvent, MonitoringReadResponse};

/// A VCD file header, containing timescale info & additional metadata
#[derive(Debug)]
pub struct Header {
    pub timescale_ps: Option<u128>,
    pub date: Option<String>,
    pub version: Option<String>,
}

/// A signal in a VCD file, of some known type & width along with a reference name
/// e.g. "wire 1 ... rx_en"
#[derive(Debug)]
pub struct Signal {
    pub signal_type: String,
    pub width: u32,
    pub reference: String,
}

/// A member item of some VCD scope, which is either another nested scope or
/// a variable definition.
#[derive(Debug)]
pub enum ScopeItem {
    Scope {
        scope_type: String,
        identifier: String,
        items: Vec<Self>,
    },
    VarDef {
        signal: Signal,
        identifier: String,
    },
}

impl ScopeItem {
    /// Get the identifiers of all variables (recursively) defined in this scope.
    pub fn var_names(&self) -> Vec<&str> {
        match self {
            ScopeItem::Scope { items, .. } => {
                let mut identifiers = Vec::new();
                for item in items {
                    identifiers.extend(item.var_names())
                }
                identifiers
            }
            ScopeItem::VarDef { identifier, .. } => {
                vec![identifier]
            }
        }
    }
}

/// A variable definition section of a VCD file, which features a list of top-level
/// scopes that encapsulate all signal variable definitions (vardefs).
#[derive(Debug)]
pub struct VarDefs {
    scopes: Vec<ScopeItem>,
}

impl VarDefs {
    /// Get the identifiers of all variables defined in the entire VarDefs section.
    pub fn var_names(&self) -> Vec<&str> {
        let mut identifiers = Vec::new();
        for scope in &self.scopes {
            identifiers.extend(scope.var_names());
        }
        identifiers
    }
}

/// Four-valued scalar logic values
#[derive(Debug)]
pub enum ScalarValue {
    Zero,
    One,
    /// Unknown / Don't Care
    X,
    /// High Impedance
    Z,
}

/// An item in the value change section of a VCD file, which can be a timestamp
/// entry, a change in the value of a signal (at the last seen timestamp), or
/// some other command (not currently supported).
#[derive(Debug)]
pub enum ValueChangeItem {
    Timestamp {
        step: u128,
    },
    Scalar {
        identifier: String,
        value: ScalarValue,
    },
    // TODO: add other VCD signal types (vector, real vars, strings)
}

/// The value change section of a VCD file, which contains a sequence of
/// value change item entries.
#[derive(Debug)]
pub struct ValueChangeSection {
    pub changes: Vec<ValueChangeItem>,
}

/// A full VCD file definition, containing at least a header (with a timescale),
/// some variable definition(s) and any recorded value change section.
#[derive(Debug)]
pub struct Vcd {
    pub header: Header,
    pub vardefs: VarDefs,
    pub value_changes: ValueChangeSection,
}

impl Vcd {
    /// Get the identifiers of all variables defined in the VCD file
    pub fn var_names(&self) -> Vec<&str> {
        self.vardefs.var_names()
    }
}

/// Errors relating to VCD encoding/dumping
#[derive(Debug, Error)]
pub enum VcdDumpError {
    #[error("Cannot represent VCD timescale {0}ps")]
    InvalidTimescale(u128),
    #[error("Timestamps out of order: {0} and {1}")]
    TimestampsOutOfOrder(u128, u128),
}

/// Struct implementing methods for writing VCD data to some io::Write
#[derive(Debug)]
pub struct VcdWriter<W: io::Write> {
    pub writer: W,
}

impl<W: io::Write> VcdWriter<W> {
    pub fn new(writer: W) -> Self {
        VcdWriter { writer }
    }

    pub fn flush(&mut self) -> Result<()> {
        self.writer.flush()?;
        Ok(())
    }

    pub fn write_vcd(&mut self, vcd: &Vcd) -> Result<()> {
        self.write_header(&vcd.header)?;
        self.write_vardefs(&vcd.vardefs)?;
        self.write_value_change_section(&vcd.value_changes, 0u128)?;
        writeln!(self.writer)?;
        Ok(())
    }

    pub fn write_header(&mut self, header: &Header) -> Result<()> {
        // TODO: perhaps avoid hardcoding for picos in the future,
        // it might be sufficient to e.g. use ns/us/ms in some cases
        if let Some(timescale_ps) = &header.timescale_ps {
            if *timescale_ps < 1 {
                bail!(VcdDumpError::InvalidTimescale(*timescale_ps));
            }
            writeln!(self.writer, "$timescale {}ps $end", timescale_ps)?;
        }
        if let Some(date) = &header.date {
            writeln!(self.writer, "$date {} $end", date)?;
        }
        if let Some(version) = &header.version {
            writeln!(self.writer, "$version {} $end", version)?;
        }
        Ok(())
    }

    pub fn write_vardefs(&mut self, vardefs: &VarDefs) -> Result<()> {
        for scope in &vardefs.scopes {
            self.write_scope_item(scope)?;
        }
        writeln!(self.writer, "$enddefinitions $end")?;
        Ok(())
    }

    pub fn write_scope_item(&mut self, scope: &ScopeItem) -> Result<()> {
        match scope {
            ScopeItem::Scope {
                scope_type,
                identifier,
                items,
            } => {
                writeln!(self.writer, "$scope {} {} $end", &scope_type, &identifier)?;
                for item in items {
                    self.write_scope_item(item)?;
                }
                writeln!(self.writer, "$upscope $end")?;
            }
            ScopeItem::VarDef { signal, identifier } => {
                writeln!(
                    self.writer,
                    "$var {} {} {} {} $end",
                    &signal.signal_type, signal.width, &identifier, &signal.reference
                )?;
            }
        }
        Ok(())
    }

    pub fn write_value_change_section(
        &mut self,
        vcs: &ValueChangeSection,
        initial_timestamp: u128,
    ) -> Result<()> {
        let mut current_timestamp = initial_timestamp;
        for (i, value_change_item) in vcs.changes.iter().enumerate() {
            if let ValueChangeItem::Timestamp { step } = value_change_item {
                if *step < current_timestamp {
                    bail!(VcdDumpError::TimestampsOutOfOrder(current_timestamp, *step));
                }
                current_timestamp = *step;
                if i != 0 {
                    writeln!(self.writer)?;
                }
            }
            self.write_value_change_item(value_change_item)?;
            write!(self.writer, " ")?;
        }
        Ok(())
    }

    pub fn write_value_change_item(&mut self, item: &ValueChangeItem) -> Result<()> {
        match item {
            ValueChangeItem::Timestamp { step } => {
                write!(self.writer, "#{}", step)?;
            }
            ValueChangeItem::Scalar { identifier, value } => {
                self.write_scalar_change(identifier, value)?;
            }
        }
        Ok(())
    }

    pub fn write_scalar_change(&mut self, identifier: &str, value: &ScalarValue) -> Result<()> {
        let value = match value {
            ScalarValue::Zero => "0",
            ScalarValue::One => "1",
            ScalarValue::X => "X",
            ScalarValue::Z => "Z",
        };
        write!(self.writer, "{}{}", value, identifier)?;
        Ok(())
    }
}

/// A helper function using a `VcdWriter` to directly dump a given Vcd to
/// a string containing equivalent VCD file contents.
pub fn dump_vcd(vcd: &Vcd) -> Result<String> {
    let mut vcd_bytes = Vec::new();
    let mut writer = VcdWriter::new(&mut vcd_bytes);
    writer.write_vcd(vcd)?;
    writer.flush()?;
    Ok(String::from_utf8(vcd_bytes).expect("Generated VCD should be UTF-8 compatible"))
}

/// Errors related to VCD decoding/parsing
#[derive(Debug, Error)]
pub enum VcdParseError {
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
    #[error("{0} is not yet supported by VCD parsing")]
    UnsupportedFeature(String),
    #[error("VCD timestamps #{0} and #{1} are out of order!")]
    TimestampsOutOfOrder(u128, u128),
    #[error("Unrecognized value {0}")]
    UnknownToken(String),
    #[error("Supplied identifier {0} does not match any defined identifier")]
    UnknownVariable(String),
}

/// Iterator for reading whitespace-separated tokens from a given io::BufRead.
/// Internally buffers the next line, returning tokens from that line.
#[derive(Debug)]
struct WhitespaceTokenizer<R: io::BufRead> {
    reader: R,
    line_buf: String,
    tokens: Vec<String>,
}

impl<R: io::BufRead> WhitespaceTokenizer<R> {
    fn new(reader: R) -> Self {
        Self {
            reader,
            line_buf: String::new(),
            tokens: Vec::new(),
        }
    }
}

impl<R: io::BufRead> Iterator for WhitespaceTokenizer<R> {
    type Item = io::Result<String>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(token) = self.tokens.pop() {
                return Some(Ok(token));
            }
            self.line_buf.clear();
            match self.reader.read_line(&mut self.line_buf) {
                Ok(0) => return None, // EOF
                Ok(_) => {}
                Err(e) => return Some(Err(e)),
            };
            // Collect tokens in reverse to efficiently pop from the back of the
            // vec, rather than the front.
            self.tokens = self
                .line_buf
                .split_whitespace()
                .map(|s| s.to_string())
                .rev()
                .collect();
        }
    }
}

/// Struct implementing methods for parsing VCD data from some io::BufRead.
#[derive(Debug)]
pub struct VcdParser<R: io::BufRead> {
    tokenizer: WhitespaceTokenizer<R>,
    identifiers: Vec<String>,
}

impl<R: io::BufRead> VcdParser<R> {
    pub fn new(reader: R) -> Self {
        VcdParser {
            tokenizer: WhitespaceTokenizer::new(reader),
            identifiers: Vec::new(),
        }
    }

    /// Get the next whitespace-separated VCD file token
    pub fn next_token(&mut self) -> Result<Option<String>, io::Error> {
        self.tokenizer.next().transpose()
    }

    pub fn parse_vcd(&mut self) -> Result<Vcd> {
        Ok(Vcd {
            header: self.parse_header()?,
            vardefs: self.parse_vardefs()?,
            value_changes: self.parse_value_change_section()?,
        })
    }

    pub fn parse_header(&mut self) -> Result<Header> {
        let mut header = Header {
            timescale_ps: None,
            date: None,
            version: None,
        };
        while let Some(token) = self.next_token()?.as_deref() {
            match token {
                "$timescale" => {
                    if header.timescale_ps.is_some() {
                        bail!(VcdParseError::MultipleDefinitions("timescale".into()));
                    }
                    // TODO: add a custom `Duration` type that supports parsing
                    // picoseconds (`ps`) rather than hacking slightly here
                    let timescale_str = self.parse_header_str("timescale")?;
                    header.timescale_ps = if timescale_str.ends_with("ps") {
                        Some(
                            timescale_str
                                .strip_suffix("ps")
                                .unwrap()
                                .trim()
                                .parse::<u128>()?,
                        )
                    } else {
                        Some(humantime::parse_duration(&timescale_str)?.as_nanos() * 1000)
                    }
                }
                "$date" => {
                    if header.date.is_some() {
                        bail!(VcdParseError::MultipleDefinitions("date".into()));
                    }
                    header.date = Some(self.parse_header_str("date")?)
                }
                "$version" => {
                    if header.version.is_some() {
                        bail!(VcdParseError::MultipleDefinitions("version".into()));
                    }
                    header.version = Some(self.parse_header_str("version")?)
                }
                "$scope" => {
                    return Ok(header);
                }
                _ => (),
            }
        }
        bail!(VcdParseError::MissingDefinition("scope".into()))
    }

    pub fn parse_header_str(&mut self, field: &str) -> Result<String> {
        let Some(mut value) = self.next_token()? else {
            bail!(VcdParseError::MissingValue(field.into()));
        };
        loop {
            match self.next_token()?.as_deref() {
                Some("$end") => return Ok(value),
                Some(next_val) => {
                    value.push(' ');
                    value.push_str(next_val);
                }
                None => bail!(VcdParseError::MissingDefinitionEnd(field.into())),
            }
        }
    }

    pub fn parse_vardefs(&mut self) -> Result<VarDefs> {
        let mut scopes = Vec::new();
        scopes.push(self.parse_scope()?);
        let mut end_seen = false;
        while let Some(token) = self.next_token()?.as_deref() {
            match (token, end_seen) {
                ("$scope", false) => {
                    scopes.push(self.parse_scope()?);
                }
                ("$scope", true) => bail!(VcdParseError::DefinitionAfterEnd),
                ("$enddefinitions", false) => {
                    end_seen = true;
                }
                ("$enddefinitions", true) => {
                    bail!(VcdParseError::MultipleDefinitions("$enddefinitions".into()))
                }
                ("$end", false) => bail!(VcdParseError::MismatchedEnd),
                ("$end", true) => return Ok(VarDefs { scopes }),
                _ => (),
            }
        }
        bail!(VcdParseError::MissingDefinition("$enddefinitions".into()))
    }

    pub fn parse_scope(&mut self) -> Result<ScopeItem> {
        let Some(scope_type) = self.next_token()? else {
            bail!(VcdParseError::MissingValue("scope type".into()));
        };
        let Some(identifier) = self.next_token()? else {
            bail!(VcdParseError::MissingValue("scope name".into()));
        };
        match self.next_token()?.as_deref() {
            Some("$end") => (),
            _ => bail!(VcdParseError::MissingDefinitionEnd("scope".into())),
        };
        let mut items = Vec::new();
        while let Some(token) = self.next_token()?.as_deref() {
            match token {
                "$scope" => {
                    items.push(self.parse_scope()?);
                }
                "$var" => {
                    items.push(self.parse_variable()?);
                }
                "$end" => {
                    return Ok(ScopeItem::Scope {
                        scope_type,
                        identifier,
                        items,
                    });
                }
                _ => (),
            }
        }
        bail!(VcdParseError::MissingDefinitionEnd("scope".into()))
    }

    pub fn parse_variable(&mut self) -> Result<ScopeItem> {
        let Some(signal_type) = self.next_token()? else {
            bail!(VcdParseError::MissingValue("signal type".into()));
        };
        let Some(var_width) = self.next_token()? else {
            bail!(VcdParseError::MissingValue("signal width".into()));
        };
        let width = var_width.parse::<u32>()?;
        let Some(identifier) = self.next_token()? else {
            bail!(VcdParseError::MissingValue("identifier".into()));
        };
        let Some(reference) = self.next_token()? else {
            bail!(VcdParseError::MissingValue("signal name".into()));
        };
        match self.next_token()?.as_deref() {
            Some("$end") => {
                self.identifiers.push(identifier.to_string());
                Ok(ScopeItem::VarDef {
                    signal: Signal {
                        signal_type,
                        width,
                        reference,
                    },
                    identifier,
                })
            }
            _ => bail!(VcdParseError::MissingDefinitionEnd("var".into())),
        }
    }

    pub fn parse_value_change_section(&mut self) -> Result<ValueChangeSection> {
        let mut changes = Vec::new();
        let current_step: u128 = 0;
        while let Some(token) = self.next_token()? {
            match token.as_str() {
                // Commands
                "$dumpvars" => {
                    bail!(VcdParseError::UnsupportedFeature("$dumpvars".into()));
                }
                "$end" => bail!(VcdParseError::MismatchedEnd),
                v if v.starts_with("$") => {
                    bail!(VcdParseError::UnsupportedFeature("commands".into()));
                }
                // Timesteps
                v if v.starts_with("#") => {
                    let step = v.strip_prefix("#").unwrap().parse::<u128>()?;
                    if step < current_step {
                        bail!(VcdParseError::TimestampsOutOfOrder(current_step, step));
                    }
                    changes.push(ValueChangeItem::Timestamp { step });
                }
                // Values
                v if v.starts_with(['0', '1', 'z', 'Z', 'x', 'X']) => {
                    changes.push(self.parse_scalar(token)?);
                }
                // TODO: add support for more VCD signal types
                v if v.starts_with(['b', 'B']) => {
                    bail!(VcdParseError::UnsupportedFeature("vector signals".into()))
                }
                v if v.starts_with(['r', 'R']) => {
                    bail!(VcdParseError::UnsupportedFeature("real vars".into()))
                }
                v if v.starts_with(['s', 'S']) => {
                    bail!(VcdParseError::UnsupportedFeature("strings".into()))
                }
                v => bail!(VcdParseError::UnknownToken(v.into())),
            }
        }
        Ok(ValueChangeSection { changes })
    }

    pub fn parse_scalar(&self, token: String) -> Result<ValueChangeItem> {
        let value = match &token[0..1] {
            "0" => ScalarValue::Zero,
            "1" => ScalarValue::One,
            "z" | "Z" => ScalarValue::Z,
            "x" | "X" => ScalarValue::X,
            v => bail!(VcdParseError::UnknownToken(v.into())),
        };
        let identifier = token[1..].to_string();
        if !self.identifiers.contains(&identifier) {
            bail!(VcdParseError::UnknownVariable(identifier));
        }
        Ok(ValueChangeItem::Scalar { identifier, value })
    }
}

/// A helper function using a `VcdParser` to directly load given VCD file
/// contents (as a &str) to an equivalent Vcd.
pub fn load_vcd(vcd: &str) -> Result<Vcd> {
    let cursor = io::Cursor::new(vcd.as_bytes());
    let mut parser = VcdParser::new(cursor);
    parser.parse_vcd()
}

/// Dump a single discrete waveform sample as a VCD value change based on the
/// previous sample. Samples are given as a slice of bytes, where each bit
/// refers to 1 value. `pin_vars` describes the variables to use for each
/// signal in LSB order (e.g. pin_vars[0] is used for byte 0 LSB, etc.)
fn dump_vcd_sample(
    pin_vars: &[String],
    timestamp: u128,
    sample: &[u8],
    prev_sample: Option<&[u8]>,
) -> Vec<ValueChangeItem> {
    let mut changes = Vec::with_capacity(pin_vars.len());
    for (i, var) in pin_vars.iter().enumerate() {
        // For each bit, calculate changes from the previous sample
        let byte_index = i / 8;
        let bit_index = i % 8;
        let sample_byte = sample.get(byte_index).unwrap_or(&0x00);
        let bit = (sample_byte >> bit_index) & 0x01;
        if let Some(prev_bytes) = prev_sample {
            let prev_byte = prev_bytes.get(byte_index).unwrap_or(&0x00);
            let prev_bit = (prev_byte >> bit_index) & 0x01;
            if prev_bit == bit {
                continue;
            }
        }
        // There has been a change in value (or this is the first sample),
        // so record the change.
        if changes.is_empty() {
            changes.push(ValueChangeItem::Timestamp { step: timestamp });
        }
        changes.push(ValueChangeItem::Scalar {
            identifier: var.to_string(),
            value: if bit != 0 {
                ScalarValue::One
            } else {
                ScalarValue::Zero
            },
        });
    }
    changes
}

/// Generate a vardefs section resulting from dumping a list of scalar (1 width)
/// write signals into a single named scope, as a helper for easily exporting
/// basic VCD files.
pub fn dump_vcd_wire_vardefs(scope: String, pin_vars: Vec<(String, Option<String>)>) -> VarDefs {
    let opentitanlib_scope = ScopeItem::Scope {
        scope_type: String::from("module"),
        identifier: scope,
        items: pin_vars
            .into_iter()
            .enumerate()
            .map(|(i, (identifier, pin))| ScopeItem::VarDef {
                signal: Signal {
                    signal_type: String::from("wire"),
                    width: 1,
                    reference: pin.unwrap_or(format!("pin_{}", i)),
                },
                identifier,
            })
            .collect::<Vec<_>>(),
    };
    VarDefs {
        scopes: vec![opentitanlib_scope],
    }
}

/// Construct a VCD from a uniformly (discretely) sampled waveform, represented by
/// a list of samples (pin values over time) and a `timescale` (sampling period).
/// Each sample is defined by a slice of bytes, where each bit index in a slice
/// refers to a single pin over each sample.
/// Variables are defined in order, corresponding to LSB-first sample order.
pub fn vcd_from_samples(
    pin_names: Vec<Option<String>>,
    timescale_ps: u128,
    samples: &[&[u8]],
) -> Result<Vcd> {
    // Generate a header sections, sequentially assigning vars '0, '1, '2, etc.
    let header = Header {
        timescale_ps: Some(timescale_ps),
        date: None,
        version: None,
    };
    let vars = &(0..pin_names.len())
        .map(|c| format!("'{}", c))
        .collect::<Vec<_>>();
    let vardefs = dump_vcd_wire_vardefs(
        String::from("opentitanlib"),
        vars.clone().into_iter().zip(pin_names).collect::<Vec<_>>(),
    );

    // Compute value changes across the uniform samples to construct the
    // value change section of the VCD
    let mut changes = Vec::new();
    let mut prev_sample = None;
    let mut last_sample_index = 0;
    let num_samples = samples.len();
    for (i, sample) in samples.iter().enumerate() {
        let value_change_items = dump_vcd_sample(vars, i as u128, sample, prev_sample);
        prev_sample = Some(sample);
        if !value_change_items.is_empty() {
            changes.extend(value_change_items);
            last_sample_index = i;
        }
    }

    // Make sure we include an ending timestamp for the final sample
    if (last_sample_index + 1) < num_samples {
        changes.push(ValueChangeItem::Timestamp {
            step: num_samples as u128 - 1,
        });
    }
    let value_changes = ValueChangeSection { changes };

    // Dump the VCD
    Ok(Vcd {
        header,
        vardefs,
        value_changes,
    })
}

/// Transform a `u64` timestamp to a time in picoseconds given some initial
/// offset timestamp measurement and a clock resolution
fn timestamp_to_picos(initial: u64, timestamp: u64, clock_res: u64) -> u128 {
    let delta = (timestamp - initial) as u128;
    delta * 1_000_000_000_000u128 / (clock_res as u128)
}

/// Transform a time in picoseconds to a `u64` timestamp relative to some
/// initial offset timestamp measurement and a clock resolution.
fn timestamp_from_picos(initial: u64, picos: u128, clock_res: u64) -> u64 {
    let delta = picos * clock_res as u128 / 1_000_000_000_000u128;
    initial + delta as u64
}

/// Construct a VCD of a waveform represented by a chronological sequence of
/// rising / falling edges (i.e. value changes) as is returned by the
/// `GpioMonitoring` interface. This includes an initial & final timestamp,
/// some initial values, and a list of edge `events`.
pub fn vcd_from_edges(
    pin_names: Vec<Option<String>>,
    clock_resolution: u64,
    initial_timestamp: u64,
    initial_values: &[bool],
    events: &[MonitoringEvent],
    final_timestamp: u64,
) -> Result<Vcd> {
    // Generate a header sections, sequentially assigning vars '0, '1, '2, etc.
    // We use a timescale of 1 picosecond to accurately represent different
    // monitoring clock resolutions.
    let header = Header {
        timescale_ps: Some(1),
        date: None,
        version: None,
    };
    let vars = &(0..pin_names.len())
        .map(|c| format!("'{}", c))
        .collect::<Vec<_>>();
    let vardefs = dump_vcd_wire_vardefs(
        String::from("opentitanlib"),
        vars.clone().into_iter().zip(pin_names).collect::<Vec<_>>(),
    );

    // Compute the value change section, which is mostly a 1-to-1 mapping
    let mut changes = Vec::new();
    // Dump the initial values
    changes.push(ValueChangeItem::Timestamp { step: 0 });
    for (&bit, var) in initial_values.iter().zip(vars.iter()) {
        changes.push(ValueChangeItem::Scalar {
            identifier: var.to_string(),
            value: if bit {
                ScalarValue::One
            } else {
                ScalarValue::Zero
            },
        });
    }
    // Edge events are essentially 1-to-1 with the VCD format
    let mut timestamp: u128 = 0;
    for event in events.iter() {
        let edge_time = timestamp_to_picos(initial_timestamp, event.timestamp, clock_resolution);
        if edge_time > timestamp {
            timestamp = edge_time;
            changes.push(ValueChangeItem::Timestamp { step: edge_time });
        }
        let index = event.signal_index as usize;
        changes.push(ValueChangeItem::Scalar {
            identifier: vars[index].clone(),
            value: if event.edge == Edge::Rising {
                ScalarValue::One
            } else {
                ScalarValue::Zero
            },
        });
    }

    // Include a final timestamp marking the final measurement
    let end_time = timestamp_to_picos(initial_timestamp, final_timestamp, clock_resolution);
    if end_time > timestamp {
        changes.push(ValueChangeItem::Timestamp { step: end_time });
    }
    let value_changes = ValueChangeSection { changes };

    // Dump the VCD
    Ok(Vcd {
        header,
        vardefs,
        value_changes,
    })
}

/// An iterator over a VCD file, which returns uniform samples of values of
/// VCD signals at every VCD time step. Depending on the delay between value
/// changes, this could result in very long iteration counts.
pub struct UniformVcdSampler {
    pub step: u128,
    pin_vars: Vec<String>,
    value_changes: std::vec::IntoIter<ValueChangeItem>,
    current_timestamp: u128,
    next_timestamp: u128,
    current_values: Vec<u8>,
    depleted: bool,
}

impl UniformVcdSampler {
    /// Create a new uniform VCD sampler. Samples every `step` steps in the VCD.
    pub fn new(vcd: Vcd, step: u128) -> Self {
        let pin_vars = vcd
            .var_names()
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>();
        let num_bytes = pin_vars.len().div_ceil(8);
        Self {
            step,
            pin_vars,
            value_changes: vcd.value_changes.changes.into_iter(),
            current_timestamp: 0u128,
            next_timestamp: 0u128,
            current_values: std::iter::repeat_n(0x00, num_bytes).collect::<Vec<_>>(),
            depleted: false,
        }
    }
}

impl Iterator for UniformVcdSampler {
    type Item = Result<Vec<u8>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Handle sampling in-between parsed timestamps
            if self.next_timestamp > self.current_timestamp {
                self.current_timestamp += self.step;
                return Some(Ok(self.current_values.clone()));
            }
            match self.value_changes.next() {
                // If we read a timestamp, sample in steps until it is reached
                Some(ValueChangeItem::Timestamp { step }) => {
                    self.next_timestamp = step;
                }
                // If we read a value, update the internal `current_values` state
                Some(ValueChangeItem::Scalar { identifier, value }) => {
                    let value = match value {
                        ScalarValue::Zero => 0,
                        ScalarValue::One => 1,
                        _ => {
                            return Some(Err(VcdParseError::UnsupportedFeature(
                                "non-binary scalars".into(),
                            )
                            .into()));
                        }
                    };
                    let Some(index) = self.pin_vars.iter().position(|id| *id == identifier) else {
                        return Some(Err(VcdParseError::UnknownVariable(identifier).into()));
                    };
                    let byte_index = index / 8;
                    let bit_index = index % 8;
                    self.current_values[byte_index] &= !(1 << bit_index);
                    self.current_values[byte_index] |= value << bit_index;
                }
                // If there are no more value changes to read, output one final
                // sample of the current values. Otherwise return `None`.
                None => {
                    if self.depleted {
                        return None;
                    }
                    self.depleted = true;
                    return Some(Ok(self.current_values.clone()));
                }
            }
        }
    }
}

/// The output of parsing a VCD to a list of edges as a `MonitoringReadResponse`,
/// which will include any parsed pin variables.
pub struct ParsedVcdEdges {
    pub pin_vars: Vec<String>,
    pub events: MonitoringReadResponse,
}

/// Parses a VCD (given its contents) to a Vec of edges (value changes), with
/// timestamps relative to the `clock_resolution` and `initial_timestamp`.
pub fn vcd_to_edges(
    vcd: Vcd,
    clock_resolution: u64,
    initial_timestamp: u64,
) -> Result<ParsedVcdEdges> {
    let pin_vars = vcd.var_names();
    let timescale = vcd
        .header
        .timescale_ps
        .expect("VCD must contain a timescale to parse to edges");

    // Parse edges from the value changes
    let mut events = Vec::new();
    let mut current_time: u128 = 0;
    let num_bytes = pin_vars.len().div_ceil(8);
    // Assume all values are initialized at 0 if not given a value at t=0.
    let mut current_values: Vec<u8> = std::iter::repeat_n(0x00, num_bytes).collect();

    for change in &vcd.value_changes.changes {
        match change {
            ValueChangeItem::Timestamp { step } => {
                current_time = *step;
            }
            ValueChangeItem::Scalar { identifier, value } => {
                let value = match value {
                    ScalarValue::Zero => 0,
                    ScalarValue::One => 1,
                    _ => bail!(VcdParseError::UnsupportedFeature(
                        "non-binary scalars".into()
                    )),
                };
                let Some(index) = pin_vars.iter().position(|id| id == identifier) else {
                    bail!(VcdParseError::UnknownVariable(identifier.into()));
                };
                let byte_index = index / 8;
                let bit_index = index % 8;
                let current_value = current_values[byte_index] >> bit_index & 0x01;
                // Only create an edge on a change of value
                if value != current_value {
                    current_values[byte_index] &= !(1 << bit_index);
                    current_values[byte_index] |= value << bit_index;
                    // Don't generate edges for initial signal values (t=0)
                    if current_time == 0 {
                        // TODO: maybe this should be parsed from a `$dumpvars` instead
                        // of `#0`, so we can have an edge at `t=0`?
                        continue;
                    }
                    let picos = current_time * timescale;
                    let timestamp =
                        timestamp_from_picos(initial_timestamp, picos, clock_resolution);
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
        }
    }

    // Determine a final timestamp for the waveform from the last step seen
    let last_picos = current_time * timescale;
    let last_timestamp = timestamp_from_picos(initial_timestamp, last_picos, clock_resolution);
    let events = MonitoringReadResponse {
        events,
        timestamp: last_timestamp,
    };
    Ok(ParsedVcdEdges {
        pin_vars: pin_vars.iter().map(|n| n.to_string()).collect(),
        events,
    })
}

#[cfg(test)]
mod test {
    use super::*;
    use std::time::Duration;

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
        samples: &[&[u8]],
        pin_names: Vec<Option<String>>,
        clock_tick: Duration,
    ) -> Result<()> {
        let vcd = dump_vcd(&vcd_from_samples(
            pin_names,
            clock_tick.as_nanos() * 1000,
            samples,
        )?)?;
        assert!(!vcd.is_empty());
        // For now this test assumes the order of bits is retained (i.e. vars
        // are parsed into sample bit indexes in the same order they are defined).
        let vcd = load_vcd(&vcd)?;
        let decoded = UniformVcdSampler::new(vcd, 1).collect::<Result<Vec<_>>>()?;
        for (decoded_sample, sample) in decoded.iter().zip(samples) {
            assert_eq!(decoded_sample, sample);
        }
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
        pin_names: Vec<Option<String>>,
    ) -> Result<()> {
        let vcd = dump_vcd(&vcd_from_edges(
            pin_names,
            clock_resolution,
            initial_timestamp,
            initial_values,
            events,
            final_timestamp,
        )?)?;
        assert!(!vcd.is_empty());
        // For now this test assumes the order of signals is retained (i.e.
        // vars are parsed into signal indexes in the order they are defined).
        let vcd = load_vcd(&vcd)?;
        let decoded = vcd_to_edges(vcd, clock_resolution, initial_timestamp)?;
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
        let sample_slices = samples.iter().map(std::slice::from_ref).collect::<Vec<_>>();
        let pin_names = Vec::from([const { None }; 3]);
        let clock_tick = Duration::from_nanos(3000);
        samples_encode_decode(&sample_slices, pin_names.clone(), clock_tick)?;

        // Example SPI waveform over 3 pins, again with a clock_tick of 3 us.
        let pin_names = vec![
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
        let sample_slices = samples.iter().map(std::slice::from_ref).collect::<Vec<_>>();
        samples_encode_decode(&sample_slices, pin_names, clock_tick)
    }

    #[test]
    fn raw_vcd_to_samples() -> Result<()> {
        let vcd = "
$timescale 1345ns $end\n\
$scope module opentitanlib $end\n\
$var wire 1 # CN_04_2 $end\n\
$var wire 1 ! CN_05_3 $end\n\
$var wire 1 ; CN_05_4 $end\n\
$var wire 1 ? CN_15_4 $end\n\
$upscope $end\n\
$enddefinitions $end\n\
#0 0# 0! 1; 0?\n\
#1 1# 1! 0;\n\
#2 0#\n\
#3 1# 0!\n\
#4 0# 1! 1;\n\
#5 1#\n\
#6 0# 0! 0; 1?\n\
#7 1# 1! 1;\n\
#8 0#\n\
#9 1# 0; 0?\n\
#10 0# 0! 1;\n\
#11 1# 1! 0;\n\
#12 0# 0!\n\
#13 1# 1!\n\
#14 0# 0! 1; 1?\n\
#15 1# 0;\n\
#16 0#\n\
#17 1# 1! 0?\n\
#18 0# 0!\n\
#19 1#\n\
#20 0#\n\
#21 1#\n\
#22 0#\n\
#23 1#\n\
#24 0#\n\
#33 1;\n\
#34 1# 1! 1?\n\
#35 0#\n\
#36 1# 0! 0; 0?\n\
#37 0#";
        let expected_pin_vars = [
            String::from("#"),
            String::from("!"),
            String::from(";"),
            String::from("?"),
        ];
        let expected_timescale = Some(1345 * 1000); // 1345 ns
        let expected_samples: [u8; 38] = [
            4, 3, 2, 1, 6, 7, 8, 15, 14, 3, 4, 3, 0, 3, 12, 9, 8, 3, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 4, 15, 14, 1, 0,
        ];

        // Load & decode the VCD, and check it matches expected contents
        let vcd = load_vcd(vcd)?;
        let decoded_pin_vars = vcd
            .var_names()
            .iter()
            .map(|n| n.to_string())
            .collect::<Vec<_>>();
        let decoded_timescale_ps = vcd.header.timescale_ps;
        let decoded_samples = UniformVcdSampler::new(vcd, 1).collect::<Result<Vec<_>>>()?;
        for expected in expected_pin_vars {
            assert!(decoded_pin_vars.contains(&expected));
        }
        assert_eq!(decoded_timescale_ps, expected_timescale);
        for (decoded_sample, sample) in decoded_samples.iter().zip(expected_samples) {
            assert_eq!(decoded_sample, std::slice::from_ref(&sample));
        }
        Ok(())
    }

    #[test]
    fn edges_waveform() -> Result<()> {
        // Random waveform over 3 pins, with a clock_tick of 1 us.
        let clock_resolution = 1_000_000;
        let initial_timestamp = 536;
        let initial_values = vec![true, false, true];
        let events = vec![
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
        ];
        let final_timestamp = 1947;
        let pin_names = Vec::from([const { None }; 3]);
        edges_encode_decode(
            clock_resolution,
            initial_timestamp,
            &initial_values,
            &events,
            final_timestamp,
            pin_names,
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
        let pin_names = vec![Some("uart_rx".into())];
        edges_encode_decode(
            clock_resolution,
            initial_timestamp,
            &initial_values,
            &events,
            final_timestamp,
            pin_names,
        )
    }

    #[test]
    fn raw_vcd_to_edges() -> Result<()> {
        let vcd = "
$timescale 1ns $end\n\
$scope module opentitanlib $end\n\
$var wire 1 # a $end\n\
$var wire 1 ! b $end\n\
$var wire 1 ; c $end\n\
$var wire 1 ? d $end\n\
$upscope $end\n\
$enddefinitions $end\n\
#0 0# 0! 1; 0?\n\
#10000 1# 1! 0;\n\
#20000 0#\n\
#30000 1# 0!\n\
#40000 0# 1! 1;\n\
#50000 1#\n\
#60000 0# 0! 0; 1?\n\
#70000 1# 1! 1;\n\
#80000 0#\n\
#90000 1# 0; 0?\n\
#100000 0# 0! 1;\n\
#110000 1# 1! 0;\n\
#120000 0# 0!\n\
#130000 1# 1!\n\
#140000 0# 0! 1; 1?\n\
#150000 1# 0;\n\
#160000 0#\n\
#170000 1# 1! 0?\n\
#180000 0# 0!\n\
#190000 1#\n\
#200000 0#\n\
#210000 1#\n\
#220000 0#\n\
#230000 1#\n\
#240000 0#\n\
#330000 1;\n\
#340000 1# 1! 1?\n\
#350000 0#\n\
#360000 1# 0! 0; 0?\n\
#100000000 0#";
        let clock_resolution = 1_000_000; // Each clock tick is 1 us.
        let initial_timestamp = 536;
        let vcd = load_vcd(vcd)?;
        let decoded = vcd_to_edges(vcd, clock_resolution, initial_timestamp)?;

        let expected_pin_vars = [
            String::from("#"),
            String::from("!"),
            String::from(";"),
            String::from("?"),
        ];
        let expected_edges = vec![
            edge(0, Edge::Rising, 546),
            edge(1, Edge::Rising, 546),
            edge(2, Edge::Falling, 546),
            edge(0, Edge::Falling, 556),
            edge(0, Edge::Rising, 566),
            edge(1, Edge::Falling, 566),
            edge(0, Edge::Falling, 576),
            edge(1, Edge::Rising, 576),
            edge(2, Edge::Rising, 576),
            edge(0, Edge::Rising, 586),
            edge(0, Edge::Falling, 596),
            edge(1, Edge::Falling, 596),
            edge(2, Edge::Falling, 596),
            edge(3, Edge::Rising, 596),
            edge(0, Edge::Rising, 606),
            edge(1, Edge::Rising, 606),
            edge(2, Edge::Rising, 606),
            edge(0, Edge::Falling, 616),
            edge(0, Edge::Rising, 626),
            edge(2, Edge::Falling, 626),
            edge(3, Edge::Falling, 626),
            edge(0, Edge::Falling, 636),
            edge(1, Edge::Falling, 636),
            edge(2, Edge::Rising, 636),
            edge(0, Edge::Rising, 646),
            edge(1, Edge::Rising, 646),
            edge(2, Edge::Falling, 646),
            edge(0, Edge::Falling, 656),
            edge(1, Edge::Falling, 656),
            edge(0, Edge::Rising, 666),
            edge(1, Edge::Rising, 666),
            edge(0, Edge::Falling, 676),
            edge(1, Edge::Falling, 676),
            edge(2, Edge::Rising, 676),
            edge(3, Edge::Rising, 676),
            edge(0, Edge::Rising, 686),
            edge(2, Edge::Falling, 686),
            edge(0, Edge::Falling, 696),
            edge(0, Edge::Rising, 706),
            edge(1, Edge::Rising, 706),
            edge(3, Edge::Falling, 706),
            edge(0, Edge::Falling, 716),
            edge(1, Edge::Falling, 716),
            edge(0, Edge::Rising, 726),
            edge(0, Edge::Falling, 736),
            edge(0, Edge::Rising, 746),
            edge(0, Edge::Falling, 756),
            edge(0, Edge::Rising, 766),
            edge(0, Edge::Falling, 776),
            edge(2, Edge::Rising, 866),
            edge(0, Edge::Rising, 876),
            edge(1, Edge::Rising, 876),
            edge(3, Edge::Rising, 876),
            edge(0, Edge::Falling, 886),
            edge(0, Edge::Rising, 896),
            edge(1, Edge::Falling, 896),
            edge(2, Edge::Falling, 896),
            edge(3, Edge::Falling, 896),
            edge(0, Edge::Falling, 100536),
        ];
        for expected in expected_pin_vars {
            assert!(decoded.pin_vars.contains(&expected));
        }
        assert_eq!(decoded.events.events, expected_edges);
        assert!(decoded.events.timestamp >= expected_edges.last().unwrap().timestamp);
        Ok(())
    }

    #[test]
    fn many_signals() -> Result<()> {
        // Test with a VCD containing 10 samples with 1024 different signals,
        // to be sure we can handle large VCDs and large samples without restriction
        const NUM_PINS: usize = 1024;
        const NUM_SAMPLES: usize = 10;
        let mut samples = Vec::new();
        let mut prng = 0x0ACECAFE;
        for _ in 0..NUM_SAMPLES {
            let mut sample = Vec::new();
            for _ in 0..NUM_PINS.div_ceil(32) {
                // xorshift32 PRNG to distribute changes across sample bitmaps.
                prng ^= prng << 13;
                prng ^= prng >> 17;
                prng ^= prng << 5;
                sample.push(prng as u8);
                sample.push((prng >> 8) as u8);
                sample.push((prng >> 16) as u8);
                sample.push((prng >> 24) as u8);
            }
            samples.push(sample);
        }
        let sample_slices = samples.iter().map(|s| s.as_ref()).collect::<Vec<_>>();
        let pin_names = Vec::from([const { None }; NUM_PINS]);
        let clock_tick = Duration::from_nanos(3000);
        samples_encode_decode(&sample_slices, pin_names, clock_tick)
    }
}
