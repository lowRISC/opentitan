// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::str::FromStr;

use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttributeMap, AttributeType};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct List {
    /// Attributes to show.
    #[arg(short, long, value_parser=AttributeType::from_str)]
    #[serde(default)]
    attribute: Vec<AttributeType>,
}

#[derive(Default, Debug, Serialize)]
pub struct ListResult {
    objects: Vec<AttributeMap>,
}

#[typetag::serde(name = "object-list")]
impl Dispatch for List {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let default_attr = [
            AttributeType::Id,
            AttributeType::Label,
            AttributeType::Class,
            AttributeType::KeyType,
        ];
        let attr = if self.attribute.is_empty() {
            default_attr.as_slice()
        } else {
            self.attribute.as_slice()
        };
        let attr = attr
            .iter()
            .map(|&a| Ok(a.try_into()?))
            .collect::<Result<Vec<cryptoki::object::AttributeType>>>()?;

        let mut result = Box::<ListResult>::default();
        for object in session.find_objects(&[])? {
            let attr = session.get_attributes(object, &attr)?;
            let attr = AttributeMap::from(attr.as_slice());
            result.objects.push(attr);
        }
        Ok(result)
    }
}
