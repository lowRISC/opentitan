// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::Result;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, ObjectClass};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Write {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, default_value = "false")]
    private: bool,
    #[arg(short, long)]
    application: Option<String>,
    #[arg(short, long)]
    template: Option<AttributeMap>,
    #[arg()]
    input: PathBuf,
}

#[typetag::serde(name = "object-write")]
impl Dispatch for Write {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;

        let mut attr = AttributeMap::default();
        let id = self
            .id
            .as_ref()
            .map_or(AttrData::None, |id| AttrData::Str(id.into()));
        let label = self
            .label
            .as_ref()
            .map_or(AttrData::None, |label| AttrData::Str(label.into()));
        if !id.is_none() {
            attr.insert(AttributeType::Id, id.clone());
        }
        if !label.is_none() {
            attr.insert(AttributeType::Label, label.clone());
        }
        if id.is_none() && label.is_none() {
            return Err(HsmError::NoSearchCriteria.into());
        }

        let result = Box::new(BasicResult {
            success: true,
            id,
            label,
            value: None,
            error: None,
        });

        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::Data),
        );
        attr.insert(AttributeType::Token, AttrData::from(true));
        attr.insert(AttributeType::Private, AttrData::from(self.private));
        if let Some(application) = &self.application {
            // Is this a bug in opensc-pkcs11 or in the Nitrokey?
            // It seems the application string needs a nul terminator.
            let mut val = application.clone();
            val.push(0 as char);
            attr.insert(AttributeType::Application, AttrData::Str(val));
        }
        if let Some(template) = &self.template {
            attr.merge(template.clone());
        }
        let value = std::fs::read(&self.input)?;
        attr.insert(AttributeType::Value, AttrData::from(value.as_slice()));
        let attr = attr.to_vec()?;
        session.create_object(&attr)?;
        Ok(result)
    }
}
