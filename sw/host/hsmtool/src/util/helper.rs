// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::object::{Attribute, ObjectHandle};
use cryptoki::session::Session;
use rand::prelude::*;
use std::convert::AsRef;
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::escape::as_hex;

/// Constructs a search template given an `id` or `label`.
pub fn search_spec(id: Option<&str>, label: Option<&str>) -> Result<Vec<Attribute>> {
    let mut attr = AttributeMap::default();
    if let Some(id) = id {
        attr.insert(AttributeType::Id, AttrData::Str(id.into()));
    }
    if let Some(label) = label {
        attr.insert(AttributeType::Label, AttrData::Str(label.into()));
    }
    if attr.is_empty() {
        return Err(HsmError::NoSearchCriteria.into());
    }
    attr.to_vec()
}

/// Returns `true` if one or more objects specified by `id` or `label` exist.
pub fn object_exists(session: &Session, id: Option<&str>, label: Option<&str>) -> Result<bool> {
    let attr = search_spec(id, label)?;
    let objects = session.find_objects(&attr)?;
    Ok(!objects.is_empty())
}

/// Returns `Ok(())` if no objects specified by `id` or `label` exist.
pub fn no_object_exists(session: &Session, id: Option<&str>, label: Option<&str>) -> Result<()> {
    if object_exists(session, id, label)? {
        Err(HsmError::ObjectExists(id.unwrap_or("").into(), label.unwrap_or("").into()).into())
    } else {
        Ok(())
    }
}

pub fn find_one_object(session: &Session, search: &[Attribute]) -> Result<ObjectHandle> {
    let mut object = session.find_objects(search)?;
    if object.is_empty() {
        let spec = AttributeMap::from(search);
        Err(HsmError::ObjectNotFound(serde_json::to_string(&spec)?).into())
    } else if object.len() > 1 {
        let spec = AttributeMap::from(search);
        Err(HsmError::TooManyObjects(object.len(), serde_json::to_string(&spec)?).into())
    } else {
        Ok(object.remove(0))
    }
}

/// Reads a file into a byte buffer.
pub fn read_file<P: AsRef<Path>>(path: P) -> Result<Vec<u8>> {
    let mut data = Vec::new();
    let mut input = File::open(path)?;
    input.read_to_end(&mut data)?;
    Ok(data)
}

/// Writes `data` to a file.
pub fn write_file<P: AsRef<Path>>(path: P, data: &[u8]) -> Result<()> {
    let mut output = File::create(path)?;
    output.write_all(data)?;
    Ok(())
}

/// Generates an 8-byte random id.
pub fn random_id() -> String {
    let id = random::<u64>();
    as_hex(&id.to_le_bytes())
}
