// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use der::{Encode, Reader, SliceReader, asn1::OctetStringRef};
use ecdsa::elliptic_curve::pkcs8::{
    self, AssociatedOid, DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey,
};
use p256::NistP256;
use p256::ecdsa::{SigningKey, VerifyingKey};

use std::convert::{AsRef, TryFrom};
use std::path::Path;

use super::KeyEncoding;
use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::helper;

fn _load_private_key(path: &Path) -> Result<SigningKey> {
    let data = helper::read_file(path)?;
    let sdata = std::str::from_utf8(&data);
    let format = match sdata {
        Ok(s) if s.contains("-----BEGIN PRIVATE KEY-----") => KeyEncoding::Pkcs8Pem,
        _ => KeyEncoding::Der,
    };
    match format {
        KeyEncoding::Pkcs8Pem => {
            SigningKey::from_pkcs8_pem(sdata.unwrap()).context("Loading private key")
        }
        _ => SigningKey::from_pkcs8_der(&data).context("Loading private key"),
    }
}

/// Loads an RSA private key from a file.  The key may be in either PKCS#1 or
/// PKCS#8 format encoded in either DER or PEM encodings.
pub fn load_private_key<P: AsRef<Path>>(path: P) -> Result<SigningKey> {
    _load_private_key(path.as_ref())
}

impl TryFrom<&SigningKey> for AttributeMap {
    type Error = HsmError;
    /// Converts an `SigningKey` into an `AttributeMap` that can be sent
    /// to an HSM.
    fn try_from(k: &SigningKey) -> std::result::Result<Self, Self::Error> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PrivateKey),
        );
        attr.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::Ec));
        attr.insert(
            AttributeType::EcParams,
            AttrData::from(NistP256::OID.to_der().unwrap().as_slice()),
        );
        attr.insert(
            AttributeType::Value,
            AttrData::from(k.to_bytes().as_slice()),
        );
        Ok(attr)
    }
}

impl TryFrom<&AttributeMap> for SigningKey {
    type Error = HsmError;
    /// Converts an `AttributeMap` into an `SigningKey`.
    fn try_from(a: &AttributeMap) -> std::result::Result<Self, Self::Error> {
        let class: ObjectClass = a
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("missing class".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = a
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("missing key_type".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::PrivateKey || key_type != KeyType::Ec {
            return Err(HsmError::KeyError("bad key type".into()));
        }
        let param: Vec<u8> = a
            .get(&AttributeType::EcParams)
            .ok_or_else(|| HsmError::KeyError("missing EC param".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let oid = NistP256::OID.to_der().unwrap();
        if param.as_slice() != oid.as_slice() {
            return Err(HsmError::KeyError("not a P256 key".into()));
        }
        let value: Vec<u8> = a
            .get(&AttributeType::Value)
            .ok_or_else(|| HsmError::KeyError("missing value".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;

        SigningKey::from_slice(&value).map_err(|e| HsmError::KeyError(format!("{e:?}")))
    }
}

fn _load_public_key(path: &Path) -> Result<VerifyingKey> {
    let data = helper::read_file(path)?;
    let sdata = std::str::from_utf8(&data);
    let format = match sdata {
        Ok(s) if s.contains("-----BEGIN PUBLIC KEY-----") => KeyEncoding::Pkcs8Pem,
        _ => KeyEncoding::Der,
    };
    match format {
        KeyEncoding::Pkcs8Pem => {
            VerifyingKey::from_public_key_pem(sdata.unwrap()).context("Loading public key")
        }
        _ => VerifyingKey::from_public_key_der(&data).context("Loading public key"),
    }
}

/// Loads an RSA public key from a file.  The key may be in either PKCS#1 or
/// PKCS#8 format encoded in either DER or PEM encodings.
pub fn load_public_key<P: AsRef<Path>>(path: P) -> Result<VerifyingKey> {
    _load_public_key(path.as_ref())
}

impl TryFrom<&VerifyingKey> for AttributeMap {
    type Error = HsmError;
    /// Converts an `VerifyingKey` into an `AttributeMap` that can be sent
    /// to an HSM.
    fn try_from(k: &VerifyingKey) -> std::result::Result<Self, Self::Error> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PublicKey),
        );
        attr.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::Ec));
        let k_sec1 = k.to_sec1_bytes();
        let k_os = OctetStringRef::new(&k_sec1)
            .or(Err(HsmError::DerError("building OctetString".into())))?;
        let k_der = k_os
            .to_der()
            .or(Err(HsmError::DerError("encoding".into())))?;
        attr.insert(AttributeType::EcPoint, AttrData::from(k_der.as_slice()));
        attr.insert(
            AttributeType::EcParams,
            AttrData::from(NistP256::OID.to_der().unwrap().as_slice()),
        );
        Ok(attr)
    }
}

impl TryFrom<&AttributeMap> for VerifyingKey {
    type Error = HsmError;
    /// Converts an `AttributeMap` into an `VerifyingKey`.
    fn try_from(a: &AttributeMap) -> std::result::Result<Self, Self::Error> {
        let class: ObjectClass = a
            .get(&AttributeType::Class)
            .ok_or_else(|| HsmError::KeyError("missing class".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let key_type: KeyType = a
            .get(&AttributeType::KeyType)
            .ok_or_else(|| HsmError::KeyError("missing key_type".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        if class != ObjectClass::PublicKey || key_type != KeyType::Ec {
            return Err(HsmError::KeyError("bad key type".into()));
        }
        let param: Vec<u8> = a
            .get(&AttributeType::EcParams)
            .ok_or_else(|| HsmError::KeyError("missing EC param".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let oid = NistP256::OID.to_der().unwrap();
        if param.as_slice() != oid.as_slice() {
            return Err(HsmError::KeyError("not a P256 key".into()));
        }

        let point_asn1: Vec<u8> = a
            .get(&AttributeType::EcPoint)
            .ok_or_else(|| HsmError::KeyError("missing EC point".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let mut reader = SliceReader::new(point_asn1.as_slice())
            .or(Err(HsmError::DerError("instanciating reader".into())))?;
        let point_os: OctetStringRef = reader
            .decode()
            .or(Err(HsmError::DerError("decoding OctetString".into())))?;

        VerifyingKey::from_sec1_bytes(point_os.as_bytes())
            .map_err(|e| HsmError::KeyError(format!("sec1: {e:?}")))
    }
}

pub fn _save_private_key<P: AsRef<Path>>(
    path: P,
    key: &SigningKey,
    enc: KeyEncoding,
) -> Result<()> {
    match enc {
        KeyEncoding::Pem | KeyEncoding::Pkcs8 | KeyEncoding::Pkcs8Pem => key
            .write_pkcs8_pem_file(path, pkcs8::LineEnding::default())
            .context("Saving private key"),
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => {
            key.write_pkcs8_der_file(path).context("Saving private key")
        }
        KeyEncoding::Pkcs1Der | KeyEncoding::Pkcs1 | KeyEncoding::Pkcs1Pem => {
            Err(HsmError::Unsupported(format!("{enc:?}")).into())
        }
    }
}

/// Saves an RSA private `key` to a file in the requested encoding.
pub fn save_private_key<P: AsRef<Path>>(path: P, key: &SigningKey, enc: KeyEncoding) -> Result<()> {
    _save_private_key(path, key, enc)
}

pub fn _save_public_key<P: AsRef<Path>>(
    path: P,
    key: &VerifyingKey,
    enc: KeyEncoding,
) -> Result<()> {
    match enc {
        KeyEncoding::Pem | KeyEncoding::Pkcs8 | KeyEncoding::Pkcs8Pem => key
            .write_public_key_pem_file(path, pkcs8::LineEnding::default())
            .context("Saving public key"),
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => key
            .write_public_key_der_file(path)
            .context("Saving public key"),
        KeyEncoding::Pkcs1Der | KeyEncoding::Pkcs1 | KeyEncoding::Pkcs1Pem => {
            Err(HsmError::Unsupported(format!("{enc:?}")).into())
        }
    }
}

/// Saves an RSA public `key` to a file in the requested encoding.
pub fn save_public_key<P: AsRef<Path>>(
    path: P,
    key: &VerifyingKey,
    enc: KeyEncoding,
) -> Result<()> {
    _save_public_key(path, key, enc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::testdata;

    const TEST2_PRIVATE_KEY: &str = r#"{
  "CKA_CLASS": "CKO_PRIVATE_KEY",
  "CKA_KEY_TYPE": "CKK_EC",
  "CKA_EC_PARAMS": "06:08:2A:86:48:CE:3D:03:01:07",
  "CKA_VALUE": "5C:6D:5F:11:6E:AE:33:00:EC:F9:12:89:47:4E:38:D5:2F:47:D4:1A:40:B2:C8:3B:2E:D1:12:74:50:3D:5E:49"
}"#;

    const TEST2_PUBLIC_KEY: &str = r#"{
  "CKA_CLASS": "CKO_PUBLIC_KEY",
  "CKA_KEY_TYPE": "CKK_EC",
  "CKA_EC_POINT": "04:41:04:1A:D2:74:FC:D8:79:7C:52:02:BF:A5:E1:0A:0E:DA:22:4C:23:68:31:8E:89:83:F6:F2:4E:40:73:3C:1E:29:35:1C:99:7D:E3:4B:93:41:F1:47:F3:D2:79:52:89:CE:80:42:D0:D1:A4:27:A3:99:5B:E0:0A:4F:5F:91:00:B9:15",
  "CKA_EC_PARAMS": "06:08:2A:86:48:CE:3D:03:01:07"
}"#;

    #[test]
    fn test_load_public_keys() -> Result<()> {
        assert!(load_public_key(testdata("key/test2_pkcs8.pub.der")).is_ok());
        //let k = load_public_key(testdata("key/test2_pkcs8.pub.der"))?;
        //save_public_key("/tmp/test2_pkcs8.pub.pem", &k, KeyEncoding::Pkcs8Pem)?;
        assert!(load_public_key(testdata("key/test2_pkcs8.pub.pem")).is_ok());
        Ok(())
    }

    #[test]
    fn test_load_private_keys() -> Result<()> {
        assert!(load_private_key(testdata("key/test2_pkcs8.der")).is_ok());
        //let k = load_private_key(testdata("key/test2_pkcs8.der"))?;
        //save_private_key("/tmp/test2_pkcs8.pem", &k, KeyEncoding::Pkcs8Pem)?;
        assert!(load_private_key(testdata("key/test2_pkcs8.pem")).is_ok());
        Ok(())
    }

    #[test]
    fn test_convert_key_to_hsm() -> Result<()> {
        let k = load_private_key(testdata("key/test2_pkcs8.pem"))?;
        let hsm = AttributeMap::try_from(&k)?;
        assert_eq!(serde_json::to_string_pretty(&hsm)?, TEST2_PRIVATE_KEY);

        let k = load_public_key(testdata("key/test2_pkcs8.pub.pem"))?;
        let hsm = AttributeMap::try_from(&k)?;
        assert_eq!(serde_json::to_string_pretty(&hsm)?, TEST2_PUBLIC_KEY);
        Ok(())
    }

    #[test]
    fn test_convert_hsm_to_key() -> Result<()> {
        let hsm = serde_json::from_str::<AttributeMap>(TEST2_PRIVATE_KEY)?;
        let kpriv = SigningKey::try_from(&hsm)?;
        let k = load_private_key(testdata("key/test2_pkcs8.pem"))?;
        assert_eq!(kpriv, k);

        let hsm = serde_json::from_str::<AttributeMap>(TEST2_PUBLIC_KEY)?;
        let kpub = VerifyingKey::try_from(&hsm)?;
        let k = load_public_key(testdata("key/test2_pkcs8.pub.pem"))?;
        assert_eq!(kpub, k);
        Ok(())
    }
}
