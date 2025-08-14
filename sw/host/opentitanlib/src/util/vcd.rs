// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
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
