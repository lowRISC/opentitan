// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Result, anyhow};
use cryptoki::mechanism::Mechanism;
use cryptoki::mechanism::vendor_defined::VendorDefinedMechanism;
use cryptoki::object::Attribute;
use cryptoki::session::Session;
use der::{Encode, EncodePem};
use serde::{Deserialize, Serialize};
use std::any::Any;
use std::fs;
use std::path::PathBuf;
use std::str::FromStr;
use x509_cert::name::Name;
use x509_cert::request::{CertReq, CertReqInfo};
use x509_cert::spki::{AlgorithmIdentifierOwned, SubjectPublicKeyInfoOwned};

use crate::commands::{BasicResult, Dispatch};
use crate::error::HsmError;
use crate::module::Module;
use crate::util::attribute::{AttributeMap, KeyType, MechanismType, ObjectClass};
use crate::util::helper;
use crate::util::key::mldsa;

#[derive(clap::Args, Debug, Serialize, Deserialize)]
pub struct ExportCsr {
    #[arg(long)]
    id: Option<String>,
    #[arg(short, long)]
    label: Option<String>,
    #[arg(long)]
    subject: String,
    #[arg(short, long)]
    output: PathBuf,
}

impl ExportCsr {
    fn run_command(&self, session: &Session) -> Result<()> {
        // Find the private key
        let mut attrs = helper::search_spec(self.id.as_deref(), self.label.as_deref())?;
        attrs.push(Attribute::Class(ObjectClass::PrivateKey.try_into()?));
        attrs.push(Attribute::KeyType(KeyType::MlDsa.try_into()?));
        let private_key = helper::find_one_object(session, &attrs)?;

        // Determine public key label
        let pub_label_string = if let Some(l) = self.label.as_deref() {
            if l.ends_with(".priv") {
                Some(l.replace(".priv", ".pub"))
            } else {
                Some(l.to_string())
            }
        } else {
            None
        };
        let pub_label = pub_label_string.as_deref();

        // Find the public key (needed for CSR)
        let mut pub_attrs = helper::search_spec(self.id.as_deref(), pub_label)?;
        pub_attrs.push(Attribute::Class(ObjectClass::PublicKey.try_into()?));
        pub_attrs.push(Attribute::KeyType(KeyType::MlDsa.try_into()?));
        let public_key = helper::find_one_object(session, &pub_attrs)?;

        // Get public key value
        let map = AttributeMap::from_object(session, public_key)?;
        let key = mldsa::MldsaVerifyingKey::try_from(&map)?;
        let pub_key_bytes = key.encode();

        // Construct Subject Name
        let subject =
            Name::from_str(&self.subject).map_err(|e| anyhow!("Invalid subject: {}", e))?;

        // Create CertReqInfo
        let algorithm = AlgorithmIdentifierOwned {
            oid: key.oid(),
            parameters: None,
        };
        let subject_public_key_info = SubjectPublicKeyInfoOwned {
            algorithm: algorithm.clone(),
            subject_public_key: x509_cert::der::asn1::BitString::from_bytes(&pub_key_bytes)
                .map_err(|e| anyhow!("Invalid public key bytes: {}", e))?,
        };

        let info = CertReqInfo {
            version: x509_cert::request::Version::V1,
            subject,
            public_key: subject_public_key_info,
            attributes: Default::default(),
        };

        // Serialize Info to sign
        let tbs_bytes = info
            .to_der()
            .map_err(|e| anyhow!("Failed to encode CertReqInfo: {}", e))?;

        // Sign the request using HSM
        // Using VendorDefinedMechanism for MLDSA signature generation
        // to avoid type mismatch with native Mechanism::MlDsa if params are tricky.
        let mechanism = Mechanism::VendorDefined(VendorDefinedMechanism::new::<()>(
            MechanismType::MlDsa.try_into()?,
            None,
        ));

        let signature_bytes = session
            .sign(&mechanism, private_key, &tbs_bytes)
            .map_err(|e| anyhow!("HSM signing failed: {}", e))?;

        let signature = x509_cert::der::asn1::BitString::from_bytes(&signature_bytes)
            .map_err(|e| anyhow!("Invalid signature bytes: {}", e))?;

        let cert_req = CertReq {
            info,
            algorithm,
            signature,
        };

        // Encode to PEM
        let pem = cert_req
            .to_pem(Default::default())
            .map_err(|e| anyhow!("Failed to encode CSR to PEM: {}", e))?;

        fs::write(&self.output, pem.as_bytes())?;

        Ok(())
    }
}

#[typetag::serde(name = "mldsa-export-csr")]
impl Dispatch for ExportCsr {
    fn run(
        &self,
        _context: &dyn Any,
        _hsm: &Module,
        session: Option<&Session>,
    ) -> Result<Box<dyn erased_serde::Serialize>> {
        let session = session.ok_or(HsmError::SessionRequired)?;
        self.run_command(session)?;
        Ok(Box::<BasicResult>::default())
    }
}
