// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{anyhow, bail, Context, Result};
use cryptoki::context::Pkcs11;
use cryptoki::object::{Attribute, ObjectHandle};
use cryptoki::session::Session;
use rsa::{RsaPrivateKey, RsaPublicKey};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::helper;
use crate::util::key::rsa::{save_private_key, save_public_key};
use crate::util::key::KeyEncoding;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Export {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(long, help = "Export the private key")]
    private: bool,
    #[arg(long, help = "Wrap the exported key a wrapping key")]
    wrap: Option<String>,
    #[arg(short, long, value_enum, default_value = "pem")]
    format: KeyEncoding,
    filename: PathBuf,
}

impl Export {
    fn export(&self, session: &Session, object: ObjectHandle) -> Result<()> {
        let map = AttributeMap::from_object(session, object)?;
        if self.private {
            match map.get(&AttributeType::PrivateExponent) {
                None => return Err(anyhow!("Key does not contain a private exponent")),
                Some(AttrData::None) => return Err(anyhow!("Private key is not exportable")),
                _ => {}
            };
            let key = RsaPrivateKey::try_from(&map)?;
            save_private_key(&self.filename, &key, self.format)?
        } else {
            let key = RsaPublicKey::try_from(&map)?;
            save_public_key(&self.filename, &key, self.format)?
        }
        Ok(())
    }

    fn wrap_key(&self, session: &Session, _object: ObjectHandle) -> Result<()> {
        let mut attrs = helper::search_spec(None, self.wrap.as_deref())?;
        attrs.push(Attribute::Class(ObjectClass::SecretKey.try_into()?));
        let _wkey = helper::find_one_object(session, &attrs).context("Find wrapping key")?;

        bail!("RSA export by wrapping is not supported yet!");
        // FIXME(cfrantz): Turn this back on when cryptoki includes the correct mechanisms.
        //let wrapped = session.wrap_key(&Mechanism::RsaPkcs, wkey, object)?;
        //helper::write_file(&self.filename, &wrapped)?;
        //Ok(())
    }
}

#[typetag::serde(name = "rsa-export")]
impl Dispatch for Export {
    fn run(
        &self,
        _context: &dyn Any,
        _pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::KeyType(KeyType::Rsa.try_into()?));
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
