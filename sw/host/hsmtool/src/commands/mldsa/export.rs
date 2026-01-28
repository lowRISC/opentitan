// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::object::{Attribute, ObjectHandle};
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fs;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::helper;
use crate::util::key::KeyEncoding;
use crate::util::wrap::{Wrap, WrapPrivateKey};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Export {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    /// Export the private key.
    #[arg(long)]
    private: bool,
    /// Wrap the exported key a wrapping key.
    #[arg(long)]
    wrap: Option<String>,
    // Wrapping key mechanism. Required when wrap is specified.
    #[arg(long, default_value = "aes-key-wrap-pad")]
    wrap_mechanism: Option<WrapPrivateKey>,
    #[arg(short, long, value_enum, default_value = "der")]
    format: KeyEncoding,
    filename: PathBuf,
}

impl Export {
    fn export(&self, session: &Session, object: ObjectHandle) -> Result<()> {
        let map = AttributeMap::from_object(session, object)?;
        let val = map.get(&AttributeType::Value).ok_or(anyhow!("Key does not contain a value"))?;
        let key_value: Vec<u8> = val.try_into()?;

        match self.format {
            KeyEncoding::Der | KeyEncoding::Pkcs8Der => {
                fs::write(&self.filename, &key_value)?;
            }
            KeyEncoding::Pem | KeyEncoding::Pkcs8Pem => {
                let label = if self.private { "PRIVATE KEY" } else { "PUBLIC KEY" };
                let pem = pem_rfc7468::encode_string(label, pem_rfc7468::LineEnding::LF, &key_value)?;
                fs::write(&self.filename, pem.as_bytes())?;
            }
             _ => return Err(anyhow!("Unsupported format for MLDSA export")),
        }
        Ok(())
    }

    fn wrap_key(&self, session: &Session, object: ObjectHandle) -> Result<()> {
        let wrapper: Wrap = self
            .wrap_mechanism
            .ok_or(anyhow!("wrap_mechanism is required when wrap is specified"))?
            .into();
        let wrapped = wrapper.wrap(session, object, self.wrap.as_deref())?;
        fs::write(&self.filename, &wrapped)?;
        Ok(())
    }
}

#[typetag::serde(name = "mldsa-export")]
impl Dispatch for Export {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::MlDsa.try_into()?));
        if self.private {
            attrs.push(Attribute::Class(ObjectClass::PrivateKey.try_into()?));
        } else {
            attrs.push(Attribute::Class(ObjectClass::PublicKey.try_into()?));
        }
        let object = helper::find_one_object(session, &attrs)?;

        if self.wrap.is_some() {
            self.wrap_key(session, object)?;
        } else {
            self.export(session, object)?;
        }
        Ok(Box::<BasicResult>::default())
    }
}
