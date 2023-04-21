// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::context::Pkcs11;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::str::FromStr;

use crate::commands::Dispatch;
use crate::error::HsmError;
use crate::util::attribute::{AttributeMap, AttributeType};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct List {
    #[arg(short, long, value_parser=AttributeType::from_str, help="Attributes to show")]
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
        _pkcs11: &Pkcs11,
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
