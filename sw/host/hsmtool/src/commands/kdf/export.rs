// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::any::Any;
use std::fs;
use std::path::PathBuf;

use anyhow::{Result, bail};
use cryptoki::object::ObjectHandle;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::helper;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Export {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// Wrap the exported key using a wrapping key.
    #[arg(long)]
    wrap: Option<String>,
    #[arg(short, long)]
    output: Option<PathBuf>,
}

impl Export {
    fn export(&self, session: &Session, object: ObjectHandle) -> Result<()> {
        let map = AttributeMap::from_object(session, object)?;

        let class: ObjectClass = map
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("Key does not have a class attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = map
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("Key does not have a key type attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::SecretKey || key_type != KeyType::GenericSecret {
            Err(HsmError::KeyError("Key is not a secret key".into()))?;
        }

        let sensitive: bool = map
            .get(&AttributeType::Sensitive)
            .ok_or_else(|| HsmError::KeyError("Key does not have a sensitive attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if sensitive {
            Err(HsmError::KeyError("Key is marked as sensitive".into()))?;
        }

        let extractable: bool = map
            .get(&AttributeType::Extractable)
            .ok_or_else(|| HsmError::KeyError("Key does not have an extractable attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if !extractable {
            Err(HsmError::KeyError("Key is not extractable".into()))?;
        }

        let key: Vec<u8> = map
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("Key does not have a value attribute".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        if let Some(output) = &self.output {
            fs::write(output, &key)?;
        }
        Ok(())
    }

    fn wrap_key(&self, _session: &Session, _object: ObjectHandle) -> Result<()> {
        bail!("Kdf key export by wrapping is not supported yet!");
    }
}

#[typetag::serde(name = "kdf-export")]
impl Dispatch for Export {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        let object = helper::find_one_object(session, attrs.as_slice())?;
        if self.wrap.is_some() {
            self.wrap_key(session, object)?;
        } else {
            self.export(session, object)?;
        }
        Ok(Box::<BasicResult>::default())
    }
}
