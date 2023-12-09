// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module provides functionality to generate substitute data for template
//! to test corner cases of the certificate generator.

use anyhow::{ensure, Result};
use rand::distributions::Distribution;
use serde::{Deserialize, Serialize};

use openssl::bn::{BigNum, BigNumContext};
use openssl::ec::{EcGroup, EcKey};
use openssl::nid::Nid;
use openssl::pkey::Private;

use crate::template::subst::{SubstData, SubstValue};
use crate::template::{EcCurve, EcPublicKeyInfo, SubjectPublicKeyInfo, Template, Value, Variable};

#[derive(Debug, Deserialize, Serialize)]
pub struct Tests {
    pub tests: Vec<SubstData>,
}

impl Tests {
    pub fn to_json(&self) -> Result<String> {
        Ok(serde_json::to_string(&self)?)
    }
}

impl Template {
    pub fn gen_tests(&self) -> Result<Tests> {
        let test = self.gen_random_test()?;
        Ok(Tests { tests: vec![test] })
    }

    // Convert a template curve name to an openssl one.
    fn ecgroup_from_curve(curve: &EcCurve) -> EcGroup {
        match curve {
            EcCurve::Prime256v1 => EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap(),
        }
    }

    fn gen_random_ec_public_key(ec_pubkey: &EcPublicKeyInfo) -> Result<SubstData> {
        // Generate a public key using openssl.
        let group = Self::ecgroup_from_curve(&ec_pubkey.curve);
        let privkey = EcKey::<Private>::generate(&group)?;
        let mut ctx = BigNumContext::new()?;
        let mut x = BigNum::new()?;
        let mut y = BigNum::new()?;
        privkey
            .public_key()
            .affine_coordinates(&group, &mut x, &mut y, &mut ctx)?;
        let mut data = SubstData::new();
        // If any of the coordinates is a variable, create a substitution for it.
        if let Value::Variable(Variable { name, convert }) = &ec_pubkey.public_key.x {
            ensure!(
                convert.is_none(),
                "cannot generate a random public key if 'x' a variable with conversion"
            );
            data.values
                .insert(name.clone(), SubstValue::ByteArray(x.to_vec()));
        }
        if let Value::Variable(Variable { name, convert }) = &ec_pubkey.public_key.y {
            ensure!(
                convert.is_none(),
                "cannot generate a random public key if 'y' a variable with conversion"
            );
            data.values
                .insert(name.clone(), SubstValue::ByteArray(y.to_vec()));
        }
        Ok(data)
    }

    fn gen_random_public_key(&self) -> Result<SubstData> {
        match &self.certificate.subject_public_key_info {
            SubjectPublicKeyInfo::EcPublicKey(ec) => Self::gen_random_ec_public_key(ec),
        }
    }

    fn gen_random_test(&self) -> Result<SubstData> {
        let mut data = SubstData::new();
        for (var, var_type) in &self.variables {
            let val = match *var_type {
                super::VariableType::ByteArray { size } => {
                    let bytes = (0..size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
                    SubstValue::ByteArray(bytes)
                }
                super::VariableType::String { size } => {
                    // FIXME: zero-terminate the string for the writer, needs to be fixed
                    let mut bytes = (0..size - 1)
                        .map(|_| rand::distributions::Alphanumeric.sample(&mut rand::thread_rng()))
                        .collect::<Vec<_>>();
                    bytes.push(0);
                    SubstValue::ByteArray(bytes)
                }
                super::VariableType::Integer { size } => {
                    if size == 4 {
                        SubstValue::Int32(rand::random::<i32>())
                    } else {
                        let bytes = (0..size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
                        SubstValue::ByteArray(bytes)
                    }
                }
                super::VariableType::Boolean => {
                    SubstValue::Boolean(rand::random::<bool>())
                }
            };
            data.values.insert(var.to_string(), val);
        }
        // We want to make sure that we generate a valid public key, otherwise
        // tools like openssl might fail to parse the certificate.
        for (key, val) in self.gen_random_public_key()?.values {
            data.values.insert(key, val);
        }
        Ok(data)
    }
}
