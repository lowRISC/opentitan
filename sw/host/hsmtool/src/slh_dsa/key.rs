// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::slh_dsa::{SlhDsaError, SlhDsaParameterSet};
use crate::util::attribute::{AttrData, AttributeMap, AttributeType};

use asn1::ParseResult;
use std::path::Path;

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
        let n = SlhDsaParameterSet::pk_bytes(pk.parameter_set);
        SlhDsaPublicKey {
            parameter_set: pk.parameter_set,
            key: pk.key[n..].to_vec(),
        }
    }
}

impl SlhDsaPrivateKey {
    fn from_bytes(parameter_set: SlhDsaParameterSet, bytes: &[u8]) -> Result<Self, SlhDsaError> {
        // An SLH-DSA private key consists of the secret key and the public key,
        // both of which are the same size.
        if bytes.len() != 2 * SlhDsaParameterSet::pk_bytes(parameter_set) {
            return Err(SlhDsaError::BadKeyLength(bytes.len()));
        }
        Ok(Self {
            parameter_set,
            key: bytes.to_vec(),
        })
    }

    pub fn from_pem_file<P: AsRef<Path>>(filename: P) -> Result<Self, SlhDsaError> {
        let s = std::fs::read_to_string(filename).map_err(SlhDsaError::Io)?;
        Self::from_pem(&s)
    }

    /// Decode an SLH-DSA private key from a PEM encoded string.
    fn from_pem(s: &str) -> Result<Self, SlhDsaError> {
        let (label, bytes) = pem_rfc7468::decode_vec(s.as_bytes()).map_err(SlhDsaError::Pem)?;

        // OpenSSL generates SLH-DSA private keys with this ASN.1 structure:
        //
        // SEQUENCE (PrivateKeyInfo)
        // |- INTEGER (Version) = 0
        // |- SEQUENCE (AlgorithmIdentifier)
        // |  +- OBJECT IDENTIFIER
        // +- OCTET STRING (PrivateKey)
        let parse: ParseResult<(asn1::ObjectIdentifier, u64, &[u8])> =
            asn1::parse(bytes.as_ref(), |d| {
                let seq: asn1::Sequence<'_> = d.read_element::<asn1::Sequence>()?;
                let inner = seq.parse(|d| {
                    let version = d.read_element::<u64>()?;
                    let seq: asn1::Sequence<'_> = d.read_element::<asn1::Sequence>()?;
                    let oid = seq.parse(|d| {
                        let oid = d.read_element::<asn1::ObjectIdentifier>()?;
                        Ok(oid)
                    })?;
                    let bytes = d.read_element::<&[u8]>()?;
                    Ok((oid, version, bytes))
                })?;
                Ok(inner)
            });

        let (oid, bytes) = match parse {
            Ok(x) => match x {
                (oid, 0, bytes) => Ok((oid, bytes)),
                _ => Err(SlhDsaError::ParseError("Unexpected version".to_string())),
            },
            Err(_) => Err(SlhDsaError::ParseError("Failed to parse".to_string())),
        }?;

        let parameter_set = SlhDsaParameterSet::try_from(oid)?;
        Self::from_bytes(parameter_set, bytes)
    }
}
