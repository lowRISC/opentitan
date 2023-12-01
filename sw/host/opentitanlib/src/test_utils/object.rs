// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use object::{Object, ObjectSection, ObjectSymbol};

/// Load a symbol's data from an object file.
pub fn symbol_data(object: &object::read::File, name: &str) -> Result<Vec<u8>> {
    let mut symbols = object.symbols();
    let symbol = symbols
        .find(|symbol| symbol.name() == Ok(name))
        .with_context(|| format!("could not find symbol {name} in ELF"))?;

    let section_index = symbol
        .section_index()
        .with_context(|| format!("symbol {name} was did not have a section index"))?;
    let section = object
        .section_by_index(section_index)
        .with_context(|| format!("could not find section containing {name}"))?;

    let offset = (symbol.address() - section.address()) as usize;
    let data = section.uncompressed_data()?;
    let data = &data[offset..][..symbol.size() as usize];

    Ok(data.to_vec())
}
