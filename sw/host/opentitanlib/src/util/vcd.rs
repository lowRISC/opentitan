// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Result};
use std::io;
use thiserror::Error;

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
                    })
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
