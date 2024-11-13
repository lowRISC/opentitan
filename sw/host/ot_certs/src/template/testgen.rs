// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//! This module provides functionality to generate substitute data for template
//! to test corner cases of the certificate generator.

use anyhow::{ensure, Result};
use rand::distributions::{DistString, Distribution, Uniform};

use openssl::bn::{BigNum, BigNumContext};
use openssl::ec::{EcGroup, EcKey};
use openssl::nid::Nid;
use openssl::pkey::Private;

use crate::template::subst::{SubstData, SubstValue};
use crate::template::{EcCurve, EcPublicKeyInfo, SubjectPublicKeyInfo, Template, Value, Variable};

// Convert a template curve name to an openssl one.
fn ecgroup_from_curve(curve: &EcCurve) -> EcGroup {
    match curve {
        EcCurve::Prime256v1 => EcGroup::from_curve_name(Nid::X9_62_PRIME256V1).unwrap(),
    }
}

impl Template {
    /// Generate a random set of data to substitute in the template to fill all the values.
    /// This generator will make sure to generate valid values for the public key if possible.
    pub fn random_test(&self) -> Result<SubstData> {
        let mut data = SubstData::new();
        for (var, var_type) in &self.variables {
            let val = match *var_type {
                super::VariableType::ByteArray { size } => {
                    let bytes = (0..size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
                    SubstValue::ByteArray(bytes)
                }
                super::VariableType::String { size } => {
                    let s = rand::distributions::Alphanumeric
                        .sample_string(&mut rand::thread_rng(), size);
                    SubstValue::String(s)
                }
                super::VariableType::Integer { size } => {
                    if size == 4 {
                        // FIXME the code does not properly distinguish between signed and
                        // unsigned integers so we must generate positive numbers for now.
                        SubstValue::Int32(rand::random::<u16>() as i32)
                    } else {
                        let bytes = (0..size).map(|_| rand::random::<u8>()).collect::<Vec<_>>();
                        SubstValue::ByteArray(bytes)
                    }
                }
                super::VariableType::Boolean => SubstValue::Boolean(rand::random::<bool>()),
            };
            data.values.insert(var.to_string(), val);
        }
        // We want to make sure that we generate valid dates, otherwise tools like
        // openssl might fail to parse the certificate.
        if let Value::Variable(Variable { name, .. }) = &self.certificate.not_before {
            data.values.insert(name.clone(), self.random_time());
        }
        if let Value::Variable(Variable { name, .. }) = &self.certificate.not_after {
            data.values.insert(name.clone(), self.random_time());
        }
        // We want to make sure that we generate a valid public key, otherwise
        // tools like openssl might fail to parse the certificate.
        for (key, val) in self.random_public_key()?.values {
            data.values.insert(key, val);
        }
        Ok(data)
    }

    fn random_time(&self) -> SubstValue {
        // The smallest possible valid GeneralizedTime is YYYYMMDDHHMMSSZ
        let mut rng = rand::thread_rng();
        let year = Uniform::from(1900..2100).sample(&mut rng);
        let month = Uniform::from(1..13).sample(&mut rng);
        let day = Uniform::from(1..29).sample(&mut rng);
        let hour = Uniform::from(0..24).sample(&mut rng);
        let minute = Uniform::from(0..60).sample(&mut rng);
        let sec = Uniform::from(0..60).sample(&mut rng);
        let time = format!("{year:04}{month:02}{day:02}{hour:02}{minute:02}{sec:02}Z");
        SubstValue::String(time)
    }

    fn random_public_key(&self) -> Result<SubstData> {
        match &self.certificate.subject_public_key_info {
            SubjectPublicKeyInfo::EcPublicKey(ec) => Self::random_ec_public_key(ec),
        }
    }

    fn random_ec_public_key(ec_pubkey: &EcPublicKeyInfo) -> Result<SubstData> {
        // Generate a public key using openssl.
        let group = ecgroup_from_curve(&ec_pubkey.curve);
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
}
