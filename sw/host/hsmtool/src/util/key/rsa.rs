// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use anyhow::{Context, Result};
use rsa::pkcs1::{
    self, DecodeRsaPrivateKey, DecodeRsaPublicKey, EncodeRsaPrivateKey, EncodeRsaPublicKey,
};
use rsa::pkcs8::{self, DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey};
use rsa::traits::{PrivateKeyParts, PublicKeyParts};
use rsa::{RsaPrivateKey, RsaPublicKey};
use std::convert::{AsRef, TryFrom};
use std::path::Path;

use super::KeyEncoding;
use crate::error::HsmError;
use crate::util::attribute::{AttrData, AttributeMap, AttributeType, KeyType, ObjectClass};
use crate::util::helper;

fn _load_private_key(path: &Path) -> Result<RsaPrivateKey> {
    let data = helper::read_file(path)?;
    let sdata = std::str::from_utf8(&data);
    let format = match sdata {
        Ok(s) if s.contains("-----BEGIN RSA PRIVATE KEY-----") => KeyEncoding::Pkcs1Pem,
        Ok(s) if s.contains("-----BEGIN PRIVATE KEY-----") => KeyEncoding::Pkcs8Pem,
        _ => KeyEncoding::Der,
    };
    match format {
        KeyEncoding::Pkcs1Pem => {
            RsaPrivateKey::from_pkcs1_pem(sdata.unwrap()).context("Loading private key")
        }
        KeyEncoding::Pkcs8Pem => {
            RsaPrivateKey::from_pkcs8_pem(sdata.unwrap()).context("Loading private key")
        }
        _ => RsaPrivateKey::from_pkcs1_der(&data)
            .or_else(|_| RsaPrivateKey::from_pkcs8_der(&data))
            .context("Loading private key"),
    }
}

/// Loads an RSA private key from a file.  The key may be in either PKCS#1 or
/// PKCS#8 format encoded in either DER or PEM encodings.
pub fn load_private_key<P: AsRef<Path>>(path: P) -> Result<RsaPrivateKey> {
    _load_private_key(path.as_ref())
}

impl TryFrom<&RsaPrivateKey> for AttributeMap {
    type Error = HsmError;
    /// Converts an `RsaPrivateKey` into an `AttributeMap` that can be sent
    /// to an HSM.
    fn try_from(k: &RsaPrivateKey) -> std::result::Result<Self, Self::Error> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PrivateKey),
        );
        attr.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::Rsa));
        attr.insert(
            AttributeType::Modulus,
            AttrData::from(k.n().to_bytes_be().as_slice()),
        );
        attr.insert(
            AttributeType::PublicExponent,
            AttrData::from(k.e().to_bytes_be().as_slice()),
        );
        attr.insert(
            AttributeType::PrivateExponent,
            AttrData::from(k.d().to_bytes_be().as_slice()),
        );
        let p = k.primes();
        attr.insert(
            AttributeType::Prime1,
            AttrData::from(p[0].to_bytes_be().as_slice()),
        );
        attr.insert(
            AttributeType::Prime2,
            AttrData::from(p[1].to_bytes_be().as_slice()),
        );
        if let Some(dp) = k.dp() {
            attr.insert(
                AttributeType::Exponent1,
                AttrData::from(dp.to_bytes_be().as_slice()),
            );
        }
        if let Some(dq) = k.dq() {
            attr.insert(
                AttributeType::Exponent2,
                AttrData::from(dq.to_bytes_be().as_slice()),
            );
        }
        if let Some(co) = k.crt_coefficient() {
            attr.insert(
                AttributeType::Coefficient,
                AttrData::from(co.to_bytes_be().as_slice()),
            );
        }
        Ok(attr)
    }
}

impl TryFrom<&AttributeMap> for RsaPrivateKey {
    type Error = HsmError;
    /// Converts an `AttributeMap` into an `RsaPrivateKey`.
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
        if class != ObjectClass::PrivateKey || key_type != KeyType::Rsa {
            return Err(HsmError::KeyError("bad key type".into()));
        }

        let n: Vec<u8> = a
            .get(&AttributeType::Modulus)
            .ok_or_else(|| HsmError::KeyError("missing modulus".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let e: Vec<u8> = a
            .get(&AttributeType::PublicExponent)
            .ok_or_else(|| HsmError::KeyError("missing public exponent".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let d: Vec<u8> = a
            .get(&AttributeType::PrivateExponent)
            .ok_or_else(|| HsmError::KeyError("missing private exponent".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let p1: Vec<u8> = a
            .get(&AttributeType::Prime1)
            .ok_or_else(|| HsmError::KeyError("missing prime1".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let p2: Vec<u8> = a
            .get(&AttributeType::Prime2)
            .ok_or_else(|| HsmError::KeyError("missing prime2".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        RsaPrivateKey::from_components(
            rsa::BigUint::from_bytes_be(&n),
            rsa::BigUint::from_bytes_be(&e),
            rsa::BigUint::from_bytes_be(&d),
            vec![
                rsa::BigUint::from_bytes_be(&p1),
                rsa::BigUint::from_bytes_be(&p2),
            ],
        )
        .map_err(|e| HsmError::KeyError(format!("{:?}", e)))
    }
}

fn _load_public_key(path: &Path) -> Result<RsaPublicKey> {
    let data = helper::read_file(path)?;
    let sdata = std::str::from_utf8(&data);
    let format = match sdata {
        Ok(s) if s.contains("-----BEGIN RSA PUBLIC KEY-----") => KeyEncoding::Pkcs1Pem,
        Ok(s) if s.contains("-----BEGIN PUBLIC KEY-----") => KeyEncoding::Pkcs8Pem,
        _ => KeyEncoding::Der,
    };
    match format {
        KeyEncoding::Pkcs1Pem => {
            RsaPublicKey::from_pkcs1_pem(sdata.unwrap()).context("Loading public key")
        }
        KeyEncoding::Pkcs8Pem => {
            RsaPublicKey::from_public_key_pem(sdata.unwrap()).context("Loading public key")
        }
        _ => RsaPublicKey::from_pkcs1_der(&data)
            .or_else(|_| RsaPublicKey::from_public_key_der(&data))
            .context("Loading public key"),
    }
}

/// Loads an RSA public key from a file.  The key may be in either PKCS#1 or
/// PKCS#8 format encoded in either DER or PEM encodings.
pub fn load_public_key<P: AsRef<Path>>(path: P) -> Result<RsaPublicKey> {
    _load_public_key(path.as_ref())
}

impl TryFrom<&RsaPublicKey> for AttributeMap {
    type Error = HsmError;
    /// Converts an `RsaPublicKey` into an `AttributeMap` that can be sent
    /// to an HSM.
    fn try_from(k: &RsaPublicKey) -> std::result::Result<Self, Self::Error> {
        let mut attr = AttributeMap::default();
        attr.insert(
            AttributeType::Class,
            AttrData::ObjectClass(ObjectClass::PublicKey),
        );
        attr.insert(AttributeType::KeyType, AttrData::KeyType(KeyType::Rsa));
        attr.insert(
            AttributeType::Modulus,
            AttrData::from(k.n().to_bytes_be().as_slice()),
        );
        attr.insert(
            AttributeType::PublicExponent,
            AttrData::from(k.e().to_bytes_be().as_slice()),
        );
        Ok(attr)
    }
}

impl TryFrom<&AttributeMap> for RsaPublicKey {
    type Error = HsmError;
    /// Converts an `AttributeMap` into an `RsaPublicKey`.
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
        if class != ObjectClass::PublicKey || key_type != KeyType::Rsa {
            return Err(HsmError::KeyError("bad key type".into()));
        }

        let n: Vec<u8> = a
            .get(&AttributeType::Modulus)
            .ok_or_else(|| HsmError::KeyError("missing modulus".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        let e: Vec<u8> = a
            .get(&AttributeType::PublicExponent)
            .ok_or_else(|| HsmError::KeyError("missing public exponent".into()))?
            .try_into()
            .map_err(HsmError::AttributeError)?;
        RsaPublicKey::new(
            rsa::BigUint::from_bytes_be(&n),
            rsa::BigUint::from_bytes_be(&e),
        )
        .map_err(|e| HsmError::KeyError(format!("{:?}", e)))
    }
}

pub fn _save_private_key<P: AsRef<Path>>(
    path: P,
    key: &RsaPrivateKey,
    enc: KeyEncoding,
) -> Result<()> {
    match enc {
        KeyEncoding::Pem | KeyEncoding::Pkcs8 | KeyEncoding::Pkcs8Pem => key
            .write_pkcs8_pem_file(path, pkcs8::LineEnding::default())
            .context("Saving private key"),
        KeyEncoding::Pkcs1 | KeyEncoding::Pkcs1Pem => key
            .write_pkcs1_pem_file(path, pkcs1::LineEnding::default())
            .context("Saving private key"),
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => {
            key.write_pkcs8_der_file(path).context("Saving private key")
        }
        KeyEncoding::Pkcs1Der => key.write_pkcs1_der_file(path).context("Saving private key"),
    }
}

/// Saves an RSA private `key` to a file in the requested encoding.
pub fn save_private_key<P: AsRef<Path>>(
    path: P,
    key: &RsaPrivateKey,
    enc: KeyEncoding,
) -> Result<()> {
    _save_private_key(path, key, enc)
}

pub fn _save_public_key<P: AsRef<Path>>(
    path: P,
    key: &RsaPublicKey,
    enc: KeyEncoding,
) -> Result<()> {
    match enc {
        KeyEncoding::Pem | KeyEncoding::Pkcs8 | KeyEncoding::Pkcs8Pem => key
            .write_public_key_pem_file(path, pkcs8::LineEnding::default())
            .context("Saving public key"),
        KeyEncoding::Pkcs1 | KeyEncoding::Pkcs1Pem => key
            .write_pkcs1_pem_file(path, pkcs1::LineEnding::default())
            .context("Saving public key"),
        KeyEncoding::Der | KeyEncoding::Pkcs8Der => key
            .write_public_key_der_file(path)
            .context("Saving public key"),
        KeyEncoding::Pkcs1Der => key.write_pkcs1_der_file(path).context("Saving public key"),
    }
}

/// Saves an RSA public `key` to a file in the requested encoding.
pub fn save_public_key<P: AsRef<Path>>(
    path: P,
    key: &RsaPublicKey,
    enc: KeyEncoding,
) -> Result<()> {
    _save_public_key(path, key, enc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testdata;

    const TEST1_PRIVATE_KEY: &str = r#"{
  "CKA_CLASS": "CKO_PRIVATE_KEY",
  "CKA_KEY_TYPE": "CKK_RSA",
  "CKA_MODULUS": "9F:04:96:98:D1:51:69:63:46:B1:4E:FB:3C:8B:62:4B:45:53:25:CC:32:ED:8E:6F:8D:7D:30:5A:A6:7E:5A:DF:E9:E7:7B:C9:1B:29:92:F2:4E:1B:AA:7D:16:14:AC:FF:48:C8:6E:03:AB:FD:0D:23:99:2B:D0:74:AE:DF:B5:E4:B7:82:25:E0:8E:D3:7D:FD:F6:D5:FC:5A:A7:39:55:87:5D:17:BD:2F:CD:CE:84:C2:84:E0:0E:93:52:68:82:D0:1F:C7:61:F3:3F:EB:8E:86:38:0E:A7:65:DA:EA:EF:F9:88:37:23:DA:03:4D:CF:95:EF:42:76:ED:C9:B1:E0:2B:5A:48:FE:08:9F:C9:81:86:EC:32:A4:19:0D:72:D0:FC:7A:C4:D3:07:87:1E:E0:D6:1B:E3:35:B8:22:AC:07:0A:A0:0F:D9:D1:43:B1:CE:3E:EF:4A:61:33:E8:B9:19:FD:65:0B:13:39:D6:37:9E:16:76:B7:0D:D2:4E:35:C2:C5:13:9B:6C:67:F4:23:B2:E4:2F:36:BF:9E:1D:D9:5B:E0:35:A0:69:77:74:49:03:7F:60:4A:90:3F:21:54:D4:F7:41:4B:31:26:39:B5:97:D0:77:D6:32:A6:2D:D9:80:52:D2:C2:6B:01:30:2D:F8:9D:9C:29:91:F5:9D:88:A9:1F:D9:46:86:3A:D7:B2:8F:1F:CE:C1:17:32:65:8B:09:3E:BF:B2:DB:58:CA:1B:CB:69:9B:69:55:EC:55:B5:91:89:04:66:9A:FA:1D:1D:4A:0F:06:21:65:78:97:58:97:58:77:E7:38:A4:FC:EC:1A:C7:A5:34:93:B7:C2:2A:CE:F0:30:35:74:BF:72:24:5B:36:F9:37:75:1F:29:04:87:77:E4:E8:34:28:C1:C4:46:3B:FA:15:DC:AB:43:05:C1:97:2C:52:4E:61:4F:55:20:65:C5:FC:70:5E:9C:AD:91:05:01:7E:1F:DC:45:21:1A:64:A6:CF:CA:64:E5:27:2B:9D",
  "CKA_PUBLIC_EXPONENT": "01:00:01",
  "CKA_PRIVATE_EXPONENT": "0B:3D:C1:8B:50:36:C8:B4:09:83:64:CC:35:69:91:66:0A:A2:A2:B2:D1:57:2C:F6:72:AD:35:7D:C9:B4:77:D0:F4:41:D6:8F:6F:01:B7:74:8A:1E:D7:64:A1:80:38:D7:90:CA:07:1E:F0:29:AD:79:5A:AD:62:7E:86:7D:E4:3C:FA:2D:08:E7:9B:93:D4:B3:09:F5:48:1C:E7:77:E7:35:85:C2:F5:19:E6:9B:11:69:B2:87:7D:4D:9E:FF:2A:34:DE:1E:3E:97:79:D4:0E:DE:AA:F7:FC:3A:4D:7E:C6:13:F6:34:17:04:7A:84:7B:11:84:19:07:26:6F:02:49:A6:29:95:D7:36:D3:06:E5:71:72:8B:EF:96:4C:21:55:A7:EC:E2:32:47:34:B4:88:86:92:46:49:08:A3:E8:D4:7E:EF:8A:EC:A6:12:BA:99:D4:25:F4:89:DE:67:CC:02:B6:95:F8:9C:60:13:BB:99:A1:1D:BC:CF:37:BD:55:7C:6D:21:F7:0D:29:47:83:68:3D:3C:9F:70:99:9B:2B:B6:10:C7:91:50:4D:DC:20:46:C2:79:AE:C0:1D:6B:01:D5:0A:95:E6:A9:E9:17:1F:AE:3B:FD:03:15:43:B6:6F:B9:52:BB:72:11:87:86:7B:B0:97:12:A7:9F:0C:1E:36:71:B6:8B:D2:9B:E8:EA:5D:C6:DF:DA:AF:F9:27:13:7E:EE:9D:DB:5F:E7:44:B6:63:0D:3D:5D:C4:5A:21:1B:00:0D:A3:E6:47:7F:CE:7D:13:F4:BC:D9:1F:09:BC:94:63:76:3D:44:9C:B0:F1:D6:8A:AD:9A:93:11:CF:4C:C7:FD:4E:EB:7E:43:09:2E:6F:00:2A:76:7A:A0:56:70:FA:3F:0A:03:A4:09:66:35:59:79:B7:D9:94:22:F2:64:B4:D0:8E:CE:04:20:07:F9:16:18:D0:95:78:BA:45:DF:3B:60:50:1D:32:56:0C:21:4D:F9:9E:42:B1:E3:FB:55:3A:79:FD:19",
  "CKA_PRIME_1": "B6:95:24:0C:A1:6D:89:CC:63:B9:4E:95:00:F1:B6:48:82:83:12:28:88:EB:9D:A8:88:53:C4:9A:BF:9F:D7:E6:A1:E7:8A:AB:0C:DA:7D:13:AD:1D:E9:11:2D:00:3F:B1:5E:49:CD:F2:3D:FE:6E:A7:1F:23:0D:EB:F7:37:38:A9:77:42:45:FE:CA:FF:32:3E:A4:BF:57:69:24:75:87:1E:D6:C7:F2:3B:EE:21:AE:6A:63:B5:F7:11:E9:94:50:C8:9B:CD:F2:B2:35:1A:41:5F:41:5A:01:A9:6E:C2:CC:35:E7:DD:03:43:01:85:E0:29:9B:7E:5F:CA:79:3C:5D:79:6F:10:AF:83:75:40:42:94:35:6E:2D:3E:15:27:E8:A2:8B:20:C9:24:CC:DF:75:15:82:D7:20:F9:BF:49:16:D3:93:44:CE:5D:9D:32:2E:87:8D:E0:CA:68:57:64:B4:30:0D:23:39:A2:16:AB:7C:02:DF:C6:67:2A:CD:CA:33:19",
  "CKA_PRIME_2": "DE:F5:B9:EC:60:53:9F:AE:09:54:BB:8D:29:60:17:F2:6C:86:07:08:9B:E8:43:AE:66:1A:AD:71:B6:B3:7A:E8:55:9B:92:45:50:FF:4B:D7:99:CF:20:1B:FC:07:EF:48:05:56:78:87:4A:3C:14:01:E2:A7:AA:62:F0:80:62:50:08:5F:51:D3:F0:97:89:74:8E:DF:B0:06:A9:F7:2B:B4:9C:62:EC:CC:A0:88:A4:1F:68:AC:79:48:38:39:CE:8B:06:99:74:2D:D4:DB:F6:B9:A3:C9:A3:E6:8B:2C:BA:C0:A3:30:48:2B:1E:0E:E9:1F:67:22:61:39:24:1B:67:7A:5D:1E:39:C4:97:48:39:38:57:05:FF:E7:56:BF:CB:54:03:CA:E9:CD:5B:7C:F2:D2:72:D9:C9:5F:F4:0C:D8:E3:E1:82:9A:26:25:02:F6:D3:48:BD:97:56:4C:3C:3B:7D:A3:44:1F:20:7C:62:8D:21:0F:11:63:32:67:16:31:25",
  "CKA_EXPONENT_1": "AD:66:6D:0B:35:D0:93:1B:32:E6:8D:94:03:86:8B:A8:C7:92:75:8F:5B:A1:F1:64:5A:BC:BB:AE:80:28:ED:61:D3:07:D4:71:68:CE:A4:15:28:C7:8C:4E:CC:9F:3C:DE:55:7E:E0:81:9C:90:E4:44:01:D5:47:E6:7F:2D:C9:B9:60:52:E7:A8:F8:DF:6E:B7:81:BD:5A:E5:B7:43:8B:25:25:B4:55:00:C7:C2:E3:23:95:38:FE:C1:DB:45:09:87:CC:38:C6:B2:AA:AE:19:C1:BE:8E:1D:9F:ED:5A:41:99:3C:70:71:25:94:EF:B1:19:B2:DC:4D:5B:3C:D2:B0:AF:A0:64:87:5B:E0:E2:3B:99:08:39:6F:EC:53:29:48:CD:FE:36:0F:F1:CC:44:B8:AC:CA:4B:47:BD:09:07:00:0F:C6:00:85:C0:F0:86:F5:1B:B6:09:F4:11:2E:56:AC:AE:29:FB:F7:43:52:26:60:AB:56:1C:D6:64:17:77:5E:19",
  "CKA_EXPONENT_2": "06:41:A0:F0:F8:17:00:A1:12:93:F5:1B:55:F0:E3:5B:23:1E:73:AE:13:29:E6:54:4B:7B:2E:28:C5:B6:AD:99:3D:65:BB:2A:04:C6:D5:2A:FC:9E:EA:48:BE:BE:BE:41:28:1D:30:0E:A3:CF:A1:C4:17:C7:1A:A9:E2:13:C8:2E:74:BD:AF:FF:21:7E:2F:16:3D:38:1B:A9:64:35:92:5D:64:12:06:91:0B:64:2A:2E:D3:72:1B:89:22:42:C4:FF:F3:B4:74:A5:20:96:F7:8A:68:05:2D:7B:37:A6:8E:AA:FF:29:48:AD:25:0F:C8:0C:E0:88:FF:6F:6A:0A:F6:D1:61:31:8A:EF:70:4B:4F:87:BC:31:67:E7:E6:F0:44:D5:5B:B1:E2:F3:A7:40:8F:53:C6:73:44:0A:54:3F:D4:0A:38:F6:C0:3A:97:C9:48:81:CF:45:BA:AC:6A:41:3A:6E:21:19:B5:41:E5:1B:A2:D8:2D:A3:10:44:86:CE:01:9D",
  "CKA_COEFFICIENT": "5F:B4:A5:27:A4:5B:F3:31:A8:6F:DD:BA:7D:D7:26:B6:2D:5C:8C:7E:C8:59:48:AB:FC:85:EA:09:D1:31:CB:31:2A:79:35:C9:AD:7C:AB:0C:41:61:44:E3:DA:C3:4A:C9:C5:72:B9:B3:B6:C0:FC:C4:E2:C9:20:4D:EC:66:07:57:22:DB:10:1C:5F:D7:3D:F6:70:27:B4:76:E5:9F:C8:92:11:9A:9F:1B:ED:1C:C3:67:0F:79:48:DF:9A:0B:50:7C:47:5D:BC:84:B9:4C:C2:7A:7C:F1:B6:0B:BB:55:93:37:56:33:F7:E6:43:68:D0:9E:D6:6D:C2:7A:14:08:50:94:7C:49:68:EB:D5:FA:88:AF:34:AF:6F:3B:75:91:EE:B5:42:B9:64:E7:95:FC:64:91:04:BA:03:AC:45:66:48:13:F4:0C:90:35:25:90:4B:E6:35:88:82:48:41:6B:4D:06:AC:8F:20:F9:82:90:3A:CF:10:7E:85:6E:3A:D8:68:48"
}"#;

    const TEST1_PUBLIC_KEY: &str = r#"{
  "CKA_CLASS": "CKO_PUBLIC_KEY",
  "CKA_KEY_TYPE": "CKK_RSA",
  "CKA_MODULUS": "9F:04:96:98:D1:51:69:63:46:B1:4E:FB:3C:8B:62:4B:45:53:25:CC:32:ED:8E:6F:8D:7D:30:5A:A6:7E:5A:DF:E9:E7:7B:C9:1B:29:92:F2:4E:1B:AA:7D:16:14:AC:FF:48:C8:6E:03:AB:FD:0D:23:99:2B:D0:74:AE:DF:B5:E4:B7:82:25:E0:8E:D3:7D:FD:F6:D5:FC:5A:A7:39:55:87:5D:17:BD:2F:CD:CE:84:C2:84:E0:0E:93:52:68:82:D0:1F:C7:61:F3:3F:EB:8E:86:38:0E:A7:65:DA:EA:EF:F9:88:37:23:DA:03:4D:CF:95:EF:42:76:ED:C9:B1:E0:2B:5A:48:FE:08:9F:C9:81:86:EC:32:A4:19:0D:72:D0:FC:7A:C4:D3:07:87:1E:E0:D6:1B:E3:35:B8:22:AC:07:0A:A0:0F:D9:D1:43:B1:CE:3E:EF:4A:61:33:E8:B9:19:FD:65:0B:13:39:D6:37:9E:16:76:B7:0D:D2:4E:35:C2:C5:13:9B:6C:67:F4:23:B2:E4:2F:36:BF:9E:1D:D9:5B:E0:35:A0:69:77:74:49:03:7F:60:4A:90:3F:21:54:D4:F7:41:4B:31:26:39:B5:97:D0:77:D6:32:A6:2D:D9:80:52:D2:C2:6B:01:30:2D:F8:9D:9C:29:91:F5:9D:88:A9:1F:D9:46:86:3A:D7:B2:8F:1F:CE:C1:17:32:65:8B:09:3E:BF:B2:DB:58:CA:1B:CB:69:9B:69:55:EC:55:B5:91:89:04:66:9A:FA:1D:1D:4A:0F:06:21:65:78:97:58:97:58:77:E7:38:A4:FC:EC:1A:C7:A5:34:93:B7:C2:2A:CE:F0:30:35:74:BF:72:24:5B:36:F9:37:75:1F:29:04:87:77:E4:E8:34:28:C1:C4:46:3B:FA:15:DC:AB:43:05:C1:97:2C:52:4E:61:4F:55:20:65:C5:FC:70:5E:9C:AD:91:05:01:7E:1F:DC:45:21:1A:64:A6:CF:CA:64:E5:27:2B:9D",
  "CKA_PUBLIC_EXPONENT": "01:00:01"
}"#;

    #[test]
    fn test_load_public_keys() -> Result<()> {
        assert!(load_public_key(testdata!("test1_pkcs8.pub.pem")).is_ok());
        assert!(load_public_key(testdata!("test1_pkcs8.pub.der")).is_ok());
        assert!(load_public_key(testdata!("test1_pkcs1.pub.pem")).is_ok());
        assert!(load_public_key(testdata!("test1_pkcs1.pub.der")).is_ok());
        Ok(())
    }

    #[test]
    fn test_load_private_keys() -> Result<()> {
        assert!(load_private_key(testdata!("test1_pkcs8.pem")).is_ok());
        assert!(load_private_key(testdata!("test1_pkcs8.der")).is_ok());
        assert!(load_private_key(testdata!("test1_pkcs1.pem")).is_ok());
        assert!(load_private_key(testdata!("test1_pkcs1.der")).is_ok());
        Ok(())
    }

    #[test]
    fn test_convert_key_to_hsm() -> Result<()> {
        let k = load_private_key(testdata!("test1_pkcs8.pem"))?;
        let hsm = AttributeMap::try_from(&k)?;
        assert_eq!(serde_json::to_string_pretty(&hsm)?, TEST1_PRIVATE_KEY);

        let k = load_public_key(testdata!("test1_pkcs8.pub.pem"))?;
        let hsm = AttributeMap::try_from(&k)?;
        assert_eq!(serde_json::to_string_pretty(&hsm)?, TEST1_PUBLIC_KEY);
        Ok(())
    }

    #[test]
    fn test_convert_hsm_to_key() -> Result<()> {
        let hsm = serde_json::from_str::<AttributeMap>(TEST1_PRIVATE_KEY)?;
        let kpriv = RsaPrivateKey::try_from(&hsm)?;
        let k = load_private_key(testdata!("test1_pkcs8.pem"))?;
        assert_eq!(kpriv, k);

        let hsm = serde_json::from_str::<AttributeMap>(TEST1_PUBLIC_KEY)?;
        let kpub = RsaPublicKey::try_from(&hsm)?;
        let k = load_public_key(testdata!("test1_pkcs8.pub.pem"))?;
        assert_eq!(kpub, k);
        Ok(())
    }
}
