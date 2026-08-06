// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use der;
use der::asn1::{ObjectIdentifier, OctetString};
use der::{Decode, Sequence};
use rsa::pkcs8;
use rsa::pkcs8::DecodePrivateKey;

use crate::slh_dsa::SlhDsaParameterSet;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};

#[derive(Clone)]
#[allow(dead_code)]
pub struct SlhDsaPrivateKey {
    parameter_set: SlhDsaParameterSet,
    key: Vec<u8>,
}

#[derive(Clone)]
#[allow(dead_code)]
pub struct SlhDsaPublicKey {
    parameter_set: SlhDsaParameterSet,
    key: Vec<u8>,
}

impl From<SlhDsaPrivateKey> for AttributeMap {
    fn from(sk: SlhDsaPrivateKey) -> Self {
        let mut map = AttributeMap::default();
        map.insert(
            AttributeType::ParameterSet,
            AttrData::from(sk.parameter_set),
        );
        map.insert(AttributeType::Value, sk.key.as_slice().into());
        map
    }
}

impl From<SlhDsaPublicKey> for AttributeMap {
    fn from(pk: SlhDsaPublicKey) -> Self {
        let mut map = AttributeMap::default();
        map.insert(
            AttributeType::ParameterSet,
            AttrData::from(pk.parameter_set),
        );
        map.insert(AttributeType::Value, pk.key.as_slice().into());
        map
    }
}

impl From<&SlhDsaPrivateKey> for SlhDsaPublicKey {
    fn from(pk: &SlhDsaPrivateKey) -> Self {
        // The private key contains a copy of the public key.
        let n = pk.parameter_set.pk_bytes();
        SlhDsaPublicKey {
            parameter_set: pk.parameter_set,
            key: pk.key[n..].to_vec(),
        }
    }
}

#[derive(Sequence)]
pub struct AlgorithmIdentifier {
    algorithm: ObjectIdentifier,
}

#[derive(Sequence)]
pub struct PrivateKey {
    version: u64,
    algorithm_identifier: AlgorithmIdentifier,
    private_key: OctetString,
}

impl Into<(u64, ObjectIdentifier, Vec<u8>)> for PrivateKey {
    fn into(self) -> (u64, ObjectIdentifier, Vec<u8>) {
        (
            self.version,
            self.algorithm_identifier.algorithm,
            self.private_key.into_bytes(),
        )
    }
}

impl DecodePrivateKey for SlhDsaPrivateKey {
    fn from_pkcs8_der(bytes: &[u8]) -> pkcs8::Result<Self> {
        let (version, oid, key) = PrivateKey::from_der(bytes)?.into();

        if version != 0 {
            return Err(pkcs8::Error::ParametersMalformed);
        }

        let parameter_set =
            SlhDsaParameterSet::try_from(oid).map_err(|_| pkcs8::Error::ParametersMalformed)?;

        if key.len() != 2 * parameter_set.pk_bytes() {
            return Err(pkcs8::Error::KeyMalformed);
        }

        let sk = Self { parameter_set, key };

        Ok(sk)
    }
}
