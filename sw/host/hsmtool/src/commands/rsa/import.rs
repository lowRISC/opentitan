// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{bail, Context, Result};
use cryptoki::context::Pkcs11;
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use std::any::Any;
use std::path::PathBuf;
use std::str::FromStr;

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, ObjectClass};
use crate::util::helper;
use crate::util::key::rsa::{load_private_key, load_public_key};

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct Import {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(short, long, help = "The key is a public key only")]
    public: bool,
    #[arg(long, help = "Attributes to apply to the public key")]
    public_attrs: Option<AttributeMap>,
    #[arg(long, help = "Attributes to apply to the private key")]
    private_attrs: Option<AttributeMap>,
    #[arg(long, help = "Unwrap the imported key with a wrapping key")]
    unwrap: Option<String>,
    filename: PathBuf,
}

impl Import {
    const PUBLIC_ATTRS: &str = r#"{
        "CKA_TOKEN": true,
        "CKA_ENCRYPT": true,
        "CKA_CLASS": "CKO_PUBLIC_KEY",
        "CKA_KEY_TYPE": "CKK_RSA",
        "CKA_VERIFY": true
    }"#;

    const PRIVATE_ATTRS: &str = r#"{
        "CKA_TOKEN": true,
        "CKA_PRIVATE": true,
        "CKA_SENSITIVE": true,
        "CKA_DECRYPT": true,
        "CKA_CLASS": "CKO_PRIVATE_KEY",
        "CKA_KEY_TYPE": "CKK_RSA",
        "CKA_SIGN": true
    }"#;

    fn unwrap_key(&self, session: &Session, _template: &AttributeMap) -> Result<()> {
        let mut attrs = helper::search_spec(None, self.unwrap.as_deref())?;
        attrs.push(Attribute::Class(ObjectClass::SecretKey.try_into()?));
        let _wkey = helper::find_one_object(session, &attrs).context("Find unwrapping key")?;

        bail!("RSA import by unwrapping is not supported yet!");
        // FIXME(cfrantz): Turn this back on when cryptoki includes the correct mechanisms.
        //let key = helper::read_file(&self.filename)?;
        //let k = session.unwrap_key(&Mechanism::RsaPkcs, wkey, &key, &template.to_vec()?)?;
        //Ok(())
    }
}

#[typetag::serde(name = "rsa-import")]
impl Dispatch for Import {
    fn run(
        &self,
        _context: &dyn Any,
        _pkcs11: &Pkcs11,
        session: Option<&Session>,
    ) -> Result<Box<dyn Annotate>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        helper::no_object_exists(session, self.id.as_deref(), self.label.as_deref())?;
        let mut public_attrs =
            AttributeMap::from_str(Self::PUBLIC_ATTRS).expect("error in PUBLIC_ATTRS");
        let mut private_attrs =
            AttributeMap::from_str(Self::PRIVATE_ATTRS).expect("error in PRIVATE_ATTRS");

        let id = AttrData::Str(self.id.as_ref().cloned().unwrap_or_else(helper::random_id));
        let result = Box::new(BasicResult {
            success: true,
            id: id.clone(),
            label: AttrData::Str(self.label.as_ref().cloned().unwrap_or_default()),
            error: None,
        });
        public_attrs.insert(AttributeType::Id, id.clone());
        public_attrs.insert(AttributeType::Label, result.label.clone());
        if let Some(tpl) = &self.public_attrs {
            public_attrs.merge(tpl.clone());
        }

        private_attrs.insert(AttributeType::Id, id);
        private_attrs.insert(AttributeType::Label, result.label.clone());
        if let Some(tpl) = &self.private_attrs {
            private_attrs.merge(tpl.clone());
        }

        if self.public {
            let key = load_public_key(&self.filename)?;
            public_attrs.merge(AttributeMap::try_from(&key)?);
            let _pubkey = session.create_object(&public_attrs.to_vec()?)?;
        } else if self.unwrap.is_some() {
            self.unwrap_key(session, &private_attrs)?;
        } else {
            let key = load_private_key(&self.filename)?;
            public_attrs.merge(AttributeMap::try_from(&key.to_public_key())?);
            let _pubkey = session.create_object(&public_attrs.to_vec()?)?;
            private_attrs.merge(AttributeMap::try_from(&key)?);
            let _privkey = session.create_object(&private_attrs.to_vec()?)?;
        }
        Ok(result)
    }
}
