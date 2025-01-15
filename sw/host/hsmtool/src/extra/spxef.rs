// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use acorn::{GenerateFlags, KeyEntry, KeyInfo, SpxInterface};
use anyhow::Result;
use cryptoki::session::Session;
use sphincsplus::{DecodeKey, EncodeKey};
use sphincsplus::{SphincsPlus, SpxDomain, SpxError, SpxPublicKey, SpxSecretKey};
use std::rc::Rc;
use std::str::FromStr;
use zeroize::Zeroizing;

use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};
use crate::util::ef::ElementaryFile;

/// SpxEf implements host-based SPHINCS+ signing with elementary files stored
/// on a PKCS#11 token.
///
/// This is not as secure as signing on an HSM, but allows secure storage of
/// the key material on a token.  Every effort is made to destroy secret key
/// material loaded to host RAM after use to prevent unintentional leaking of
/// keys.
pub struct SpxEf {
    session: Rc<Session>,
}

impl SpxEf {
    const APPLICATION: &'static str = "hsmtool-spx";

    pub fn new(session: Rc<Session>) -> Box<Self> {
        Box::new(Self { session })
    }

    fn load_key(&self, alias: &str) -> Result<SpxSecretKey> {
        let mut search = AttributeMap::default();
        search.insert(AttributeType::Label, AttrData::Str(alias.into()));
        let mut ef = ElementaryFile::find(&self.session, search)?;
        if ef.is_empty() {
            return Err(HsmError::ObjectNotFound(alias.into()).into());
        } else if ef.len() > 1 {
            return Err(HsmError::TooManyObjects(ef.len(), alias.into()).into());
        }
        let ef = ef.remove(0);
        if let Some(app) = &ef.application {
            match app.split_once(':') {
                Some((Self::APPLICATION, _algo)) => {
                    let data = Zeroizing::new(String::from_utf8(ef.read(&self.session)?)?);
                    return Ok(SpxSecretKey::from_pem(data.as_str())?);
                }
                Some((_, _)) | None => {
                    return Err(HsmError::UnknownApplication(app.into()).into());
                }
            }
        }
        Err(HsmError::UnknownApplication("<none>".into()).into())
    }
}

impl SpxInterface for SpxEf {
    /// Get the version of the backend.
    fn get_version(&self) -> Result<String> {
        Ok(String::from("PKCS#11 ElementaryFiles 0.0.1"))
    }

    /// List keys known to the backend.
    fn list_keys(&self) -> Result<Vec<KeyEntry>> {
        let mut result = Vec::new();
        for file in ElementaryFile::list(&self.session)? {
            if let Some(app) = file.application {
                if let Some((Self::APPLICATION, algo)) = app.split_once(':') {
                    result.push(KeyEntry {
                        alias: file.name.clone(),
                        hash: None,
                        algorithm: algo.into(),
                        ..Default::default()
                    });
                }
            }
        }
        Ok(result)
    }

    /// Get the public key info.
    fn get_key_info(&self, alias: &str) -> Result<KeyInfo> {
        let sk = self.load_key(alias)?;
        let pk = SpxPublicKey::from(&sk);

        Ok(KeyInfo {
            hash: "".into(),
            algorithm: pk.algorithm().to_string(),
            domain: None,
            public_key: pk.as_bytes().to_vec(),
            private_blob: Vec::new(),
        })
    }

    /// Generate a key pair.
    fn generate_key(
        &self,
        alias: &str,
        algorithm: &str,
        _domain: SpxDomain,
        _token: &str,
        flags: GenerateFlags,
    ) -> Result<KeyEntry> {
        let mut search = AttributeMap::default();
        search.insert(AttributeType::Label, AttrData::Str(alias.into()));
        let ef = ElementaryFile::find(&self.session, search)?;
        if flags.contains(GenerateFlags::OVERWRITE) {
            if ef.len() <= 1 {
                // delete files
            } else {
                return Err(HsmError::TooManyObjects(ef.len(), alias.into()).into());
            }
        } else if !ef.is_empty() {
            return Err(HsmError::ObjectExists("<none>".into(), alias.into()).into());
        }

        let (sk, _) = SpxSecretKey::new_keypair(SphincsPlus::from_str(algorithm)?)?;
        let app = format!("{}:{}", Self::APPLICATION, sk.algorithm());
        let skf = ElementaryFile::new(alias.into())
            .application(app)
            .private(true);
        let encoded = Zeroizing::new(sk.to_pem()?);
        skf.write(&self.session, encoded.as_bytes())?;

        let private_key = if flags.contains(GenerateFlags::EXPORT_PRIVATE) {
            sk.as_bytes().to_vec()
        } else {
            Vec::new()
        };

        Ok(KeyEntry {
            alias: alias.into(),
            hash: Some("".into()),
            algorithm: sk.algorithm().to_string(),
            domain: None,
            private_blob: Vec::new(),
            private_key,
        })
    }

    /// Import a key pair.
    fn import_keypair(
        &self,
        alias: &str,
        algorithm: &str,
        _domain: SpxDomain,
        _token: &str,
        overwrite: bool,
        public_key: &[u8],
        private_key: &[u8],
    ) -> Result<KeyEntry> {
        let mut search = AttributeMap::default();
        search.insert(AttributeType::Label, AttrData::Str(alias.into()));
        let ef = ElementaryFile::find(&self.session, search)?;
        if overwrite {
            if ef.len() <= 1 {
                // delete files
            } else {
                return Err(HsmError::TooManyObjects(ef.len(), alias.into()).into());
            }
        } else if !ef.is_empty() {
            return Err(HsmError::ObjectExists("<none>".into(), alias.into()).into());
        }

        let sk = SpxSecretKey::from_bytes(SphincsPlus::from_str(algorithm)?, private_key)?;
        let pk = SpxPublicKey::from(&sk);
        if public_key != pk.as_bytes() {
            return Err(HsmError::KeyError("secret/public key mismatch".into()).into());
        }
        let app = format!("{}:{}", Self::APPLICATION, sk.algorithm());
        let skf = ElementaryFile::new(alias.into())
            .application(app)
            .private(true);
        let encoded = Zeroizing::new(sk.to_pem()?);
        skf.write(&self.session, encoded.as_bytes())?;

        Ok(KeyEntry {
            alias: alias.into(),
            hash: None,
            algorithm: sk.algorithm().to_string(),
            domain: None,
            private_blob: Vec::new(),
            private_key: Vec::new(),
        })
    }

    /// Sign a message.
    fn sign(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
    ) -> Result<Vec<u8>> {
        let alias = alias.ok_or(HsmError::NoSearchCriteria)?;
        if key_hash.is_some() {
            log::warn!("ignored key_hash {key_hash:?}");
        }
        let sk = self.load_key(alias)?;
        Ok(sk.sign(domain, message)?)
    }

    /// Verify a message.
    fn verify(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool> {
        let alias = alias.ok_or(HsmError::NoSearchCriteria)?;
        if key_hash.is_some() {
            log::warn!("ignored key_hash {key_hash:?}");
        }
        let sk = self.load_key(alias)?;
        let pk = SpxPublicKey::from(&sk);
        match pk.verify(domain, signature, message) {
            Ok(()) => Ok(true),
            Err(SpxError::BadSignature) => Ok(false),
            Err(e) => Err(e.into()),
        }
    }
}
