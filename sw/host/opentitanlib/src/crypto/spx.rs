// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::io::{Read, Write};
use std::path::Path;
use std::str::FromStr;

use anyhow::{Context, Result, anyhow, bail, ensure};
use clap::ValueEnum;
use pkcs8::{DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey, LineEnding};
use serde::{Deserialize, Serialize};
use serde_annotate::Annotate;
use strum::EnumIter;

use super::Error;
use sphincsplus::{DecodeKey, EncodeKey, SphincsPlus, SpxPublicKey, SpxSecretKey};

/// Modes of operation for loading & resolving SPHINCS+/SLH-DSA public keys.
#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SpxKeyLoadingMode {
    /// Only try to load the key as a public key. Intended to enforce
    /// more strict key hygiene and the principle of least privilege.
    #[default]
    PublicOnly,
    /// If loading the key as a public key fails, try loading it as a private
    /// key instead, and extract the public key from the private key.
    Fallback,
}

/// Formats that can be used to represent SPX (SPHINCS+ or SLH-DSA) keys.
#[derive(
    Default, Debug, Clone, Copy, PartialEq, Eq, ValueEnum, EnumIter, Serialize, Deserialize,
)]
pub enum SpxKeyFormat {
    /// A custom RAW PEM format used by OpenTitan pre-standardization of SLH-DSA.
    /// A legacy format which is used only for SPHINCS+ signing.
    #[default]
    #[serde(rename = "pre-standard-pem")]
    PreStandardPem,
    /// PEM format: PKCS#8 for private keys, and `SubjectPublicKeyInfo` for public keys.
    /// A standard format used for SLH-DSA signing.
    #[serde(rename = "pkcs8-pem")]
    Pkcs8Pem,
    /// DER format: PKCS#8 for private keys, and `SubjectPublicKeyInfo` for public keys.
    /// A standard format used for SLH-DSA signing.
    #[serde(rename = "pkcs8-der")]
    Pkcs8Der,
}

impl std::fmt::Display for SpxKeyFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PreStandardPem => write!(f, "pre-standard-pem"),
            Self::Pkcs8Pem => write!(f, "pkcs8-pem"),
            Self::Pkcs8Der => write!(f, "pkcs8-der"),
        }
    }
}

impl SpxKeyFormat {
    /// Standard file extension for a private key in this format.
    pub fn ext(&self) -> &'static str {
        match self {
            Self::PreStandardPem | Self::Pkcs8Pem => "pem",
            Self::Pkcs8Der => "der",
        }
    }
    /// Standard file extension for a public key in this format.
    pub fn pub_ext(&self) -> String {
        format!("pub.{}", self.ext())
    }

    /// Load a SPHINCS+/SLH-DSA private key of a known format from its raw bytes.
    pub fn private_key_from_bytes<'a>(&self, input: &'a [u8]) -> Result<SpxSecretKey> {
        match self {
            Self::PreStandardPem => {
                return SpxSecretKey::from_pem_bytes(input).map_err(|e| anyhow!(e));
            }
            // For standard PKCS8 forms, we first try SHA2, and then SHAKE.
            // This is not the most efficient approach - a better way would be
            // to manually parse out the OID depending on the format and use
            // to determine the algorithm. This would be much more complicated,
            // however, so we keep things simple here unless deemed necessary.
            Self::Pkcs8Pem => {
                let pem =
                    std::str::from_utf8(input).context("Failed to read PEM contents as UTF-8")?;
                if let Ok(pk) = slh_dsa::SigningKey::<slh_dsa::Sha2_128s>::from_pkcs8_pem(pem) {
                    return SpxSecretKey::from_bytes(SphincsPlus::Sha2128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
                if let Ok(pk) = slh_dsa::SigningKey::<slh_dsa::Shake128s>::from_pkcs8_pem(pem) {
                    return SpxSecretKey::from_bytes(SphincsPlus::Shake128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
            }
            Self::Pkcs8Der => {
                if let Ok(pk) = slh_dsa::SigningKey::<slh_dsa::Sha2_128s>::from_pkcs8_der(input) {
                    return SpxSecretKey::from_bytes(SphincsPlus::Sha2128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
                if let Ok(pk) = slh_dsa::SigningKey::<slh_dsa::Shake128s>::from_pkcs8_der(input) {
                    return SpxSecretKey::from_bytes(SphincsPlus::Shake128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
            }
        };
        bail!("failed to parse SPHINCS+/SLH-DSA private key in the {self:?} format")
    }

    /// Load a SPHINCS+/SLH-DSA public key of a known format from its raw bytes.
    pub fn public_key_from_bytes<'a>(&self, input: &'a [u8]) -> Result<SpxPublicKey> {
        match self {
            Self::PreStandardPem => {
                return SpxPublicKey::from_pem_bytes(input).map_err(|e| anyhow!(e));
            }
            // For standard SPKI forms, we first try SHA2, and then SHAKE.
            // This is not the most efficient approach - a better way would be
            // to manually parse out the OID depending on the format and use
            // to determine the algorithm. This would be much more complicated,
            // however, so we keep things simple here unless deemed necessary.
            Self::Pkcs8Pem => {
                let pem =
                    std::str::from_utf8(input).context("Failed to read PEM contents as UTF-8")?;
                if let Ok(pk) =
                    slh_dsa::VerifyingKey::<slh_dsa::Sha2_128s>::from_public_key_pem(pem)
                {
                    return SpxPublicKey::from_bytes(SphincsPlus::Sha2128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
                if let Ok(pk) =
                    slh_dsa::VerifyingKey::<slh_dsa::Shake128s>::from_public_key_pem(pem)
                {
                    return SpxPublicKey::from_bytes(SphincsPlus::Shake128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
            }
            Self::Pkcs8Der => {
                if let Ok(pk) =
                    slh_dsa::VerifyingKey::<slh_dsa::Sha2_128s>::from_public_key_der(input)
                {
                    return SpxPublicKey::from_bytes(SphincsPlus::Sha2128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
                if let Ok(pk) =
                    slh_dsa::VerifyingKey::<slh_dsa::Shake128s>::from_public_key_der(input)
                {
                    return SpxPublicKey::from_bytes(SphincsPlus::Shake128sSimple, &pk.to_bytes())
                        .map_err(|e| anyhow!(e));
                }
            }
        };
        bail!("failed to parse SPHINCS+/SLH-DSA public key in the {self:?} format")
    }
}

/// Load a SPHINCS+/SLH-DSA private key of an unknown format from its raw bytes.
pub fn load_spx_private_key_from_bytes<'a>(input: &'a [u8]) -> Result<SpxSecretKey> {
    // Simply try the variants in the order: Pre-Standardization -> Pem -> Der
    SpxKeyFormat::PreStandardPem
        .private_key_from_bytes(input)
        .or_else(|_| SpxKeyFormat::Pkcs8Pem.private_key_from_bytes(input))
        .or_else(|_| SpxKeyFormat::Pkcs8Der.private_key_from_bytes(input))
        .map_err(|_| anyhow!("failed to parse SPHINCS+/SLH-DSA private key in any known format"))
}

/// Load a SPHINCS+/SLH-DSA private key of an unknown format from a file.
pub fn load_spx_private_key(path: impl AsRef<Path>) -> Result<SpxSecretKey> {
    let path = path.as_ref();
    let data = std::fs::read(path).with_context(|| format!("Failed to read file: {path:?}"))?;
    load_spx_private_key_from_bytes(&data)
}

/// Write a SPHINCS+/SLH-DSA private key to a given file in the specified format.
pub fn save_spx_private_key(
    key: &SpxSecretKey,
    path: impl AsRef<Path>,
    format: SpxKeyFormat,
) -> Result<()> {
    let path = path.as_ref();
    match format {
        SpxKeyFormat::PreStandardPem => key.write_pem_file(path).with_context(|| {
            format!("Failed to write pre-standardization OpenTitan RAW PEM to {path:?}")
        })?,
        SpxKeyFormat::Pkcs8Pem | SpxKeyFormat::Pkcs8Der => match key.algorithm() {
            SphincsPlus::Shake128sSimple => {
                let pk = slh_dsa::SigningKey::<slh_dsa::Shake128s>::try_from(key.as_bytes())
                    .map_err(|e| anyhow!("Failed to convert to slh_dsa SigningKey: {:?}", e))?;
                match format {
                    SpxKeyFormat::Pkcs8Pem => pk
                        .write_pkcs8_pem_file(path, LineEnding::default())
                        .with_context(|| format!("Failed to write PKCS#8 PEM to {path:?}"))?,
                    SpxKeyFormat::Pkcs8Der => pk
                        .write_pkcs8_der_file(path)
                        .with_context(|| format!("Failed to write PKCS#8 DER to {path:?}"))?,
                    _ => unreachable!(),
                }
            }
            SphincsPlus::Sha2128sSimple => {
                let pk = slh_dsa::SigningKey::<slh_dsa::Sha2_128s>::try_from(key.as_bytes())
                    .map_err(|e| anyhow!("Failed to convert to slh_dsa SigningKey: {:?}", e))?;
                match format {
                    SpxKeyFormat::Pkcs8Pem => pk
                        .write_pkcs8_pem_file(path, LineEnding::default())
                        .with_context(|| format!("Failed to write PKCS#8 PEM to {path:?}"))?,
                    SpxKeyFormat::Pkcs8Der => pk
                        .write_pkcs8_der_file(path)
                        .with_context(|| format!("Failed to write PKCS#8 DER to {path:?}"))?,
                    _ => unreachable!(),
                }
            }
        },
    }
    Ok(())
}

/// Load a SPHINCS+/SLH-DSA public key of an unknown format from its raw bytes.
/// Depending on the specified `mode`, this may optionally attempt to load the
/// bytes as a private key (as in [`load_spx_private_key_from_bytes`]) upon failing
/// to load as a public key.
pub fn load_spx_public_key_from_bytes<'a>(
    input: &'a [u8],
    mode: SpxKeyLoadingMode,
) -> Result<SpxPublicKey> {
    // Simply try the variants in the order: Pre-Standardization -> Pem -> Der
    let public_key = SpxKeyFormat::PreStandardPem
        .public_key_from_bytes(input)
        .or_else(|_| SpxKeyFormat::Pkcs8Pem.public_key_from_bytes(input))
        .or_else(|_| SpxKeyFormat::Pkcs8Der.public_key_from_bytes(input))
        .map_err(|_| anyhow!("failed to parse SPHINCS+/SLH-DSA public key in any known format"));
    if public_key.is_ok() || mode == SpxKeyLoadingMode::PublicOnly {
        return public_key;
    }
    match load_spx_private_key_from_bytes(input) {
        Ok(private_key) => Ok(SpxPublicKey::from(&private_key)),
        Err(_) => Err(anyhow!(
            "failed to parse SPHINCS+/SLH-DSA public key in any known format"
        )),
    }
}

/// Load a SPHINCS+/SLH-DSA public key of an unknown format from a file.
/// Depending on the specified `mode`, this may optionally attempt to load the
/// file as a private key (as in [`load_spx_private_key`]) upon failing to
/// load as a public key.
pub fn load_spx_public_key(
    path: impl AsRef<Path>,
    mode: SpxKeyLoadingMode,
) -> Result<SpxPublicKey> {
    let path = path.as_ref();
    let data = std::fs::read(path).with_context(|| format!("Failed to read file: {path:?}"))?;
    load_spx_public_key_from_bytes(&data, mode)
}

/// Write a SPHINCS+/SLH-DSA public key to a given file in the specified format.
pub fn save_spx_public_key(
    key: &SpxPublicKey,
    path: impl AsRef<Path>,
    format: SpxKeyFormat,
) -> Result<()> {
    let path = path.as_ref();
    match format {
        SpxKeyFormat::PreStandardPem => key.write_pem_file(path).with_context(|| {
            format!("Failed to write pre-standardization OpenTitan RAW PEM to {path:?}")
        })?,
        SpxKeyFormat::Pkcs8Pem | SpxKeyFormat::Pkcs8Der => match key.algorithm() {
            SphincsPlus::Shake128sSimple => {
                let pk = slh_dsa::VerifyingKey::<slh_dsa::Shake128s>::try_from(key.as_bytes())
                    .map_err(|e| anyhow!("Failed to convert to slh_dsa VerifyingKey: {:?}", e))?;
                match format {
                    SpxKeyFormat::Pkcs8Pem => pk
                        .write_public_key_pem_file(path, LineEnding::default())
                        .with_context(|| format!("Failed to write SPKI PEM to {path:?}"))?,
                    SpxKeyFormat::Pkcs8Der => pk
                        .write_public_key_der_file(path)
                        .with_context(|| format!("Failed to write SPKI DER to {path:?}"))?,
                    _ => unreachable!(),
                }
            }
            SphincsPlus::Sha2128sSimple => {
                let pk = slh_dsa::VerifyingKey::<slh_dsa::Sha2_128s>::try_from(key.as_bytes())
                    .map_err(|e| anyhow!("Failed to convert to slh_dsa VerifyingKey: {:?}", e))?;
                match format {
                    SpxKeyFormat::Pkcs8Pem => pk
                        .write_public_key_pem_file(path, LineEnding::default())
                        .with_context(|| format!("Failed to write SPKI PEM to {path:?}"))?,
                    SpxKeyFormat::Pkcs8Der => pk
                        .write_public_key_der_file(path)
                        .with_context(|| format!("Failed to write SPKI DER to {path:?}"))?,
                    _ => unreachable!(),
                }
            }
        },
    }
    Ok(())
}

#[derive(Debug, Serialize, Deserialize, Annotate, PartialEq)]
pub struct SpxRawPublicKey {
    #[serde(with = "serde_bytes")]
    #[annotate(format = hexstr)]
    pub key: Vec<u8>,
}

impl Default for SpxRawPublicKey {
    fn default() -> Self {
        Self { key: vec![0; 32] }
    }
}

impl TryFrom<&sphincsplus::SpxPublicKey> for SpxRawPublicKey {
    type Error = Error;
    fn try_from(v: &SpxPublicKey) -> Result<Self, Self::Error> {
        Ok(Self {
            key: v.as_bytes().to_vec(),
        })
    }
}

impl TryFrom<sphincsplus::SpxPublicKey> for SpxRawPublicKey {
    type Error = Error;
    fn try_from(v: SpxPublicKey) -> Result<Self, Self::Error> {
        (&v).try_into()
    }
}

impl FromStr for SpxRawPublicKey {
    type Err = Error;

    // Note: this function is a bit unintuitive - it loads from the file path,
    // not the string contents.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let key = load_spx_public_key(s, SpxKeyLoadingMode::Fallback)
            .with_context(|| format!("Failed to load {s}"))
            .map_err(Error::Other)?;
        SpxRawPublicKey::try_from(&key)
    }
}

impl SpxRawPublicKey {
    pub const SIZE: usize = 32;
    pub fn read(src: &mut impl Read) -> Result<Self> {
        let mut key = Self::default();
        key.key.resize(32, 0);
        src.read_exact(&mut key.key)?;
        Ok(key)
    }
    pub fn write(&self, dest: &mut impl Write) -> Result<()> {
        ensure!(
            self.key.len() == Self::SIZE,
            Error::InvalidPublicKey(anyhow!("bad key length: {}", self.key.len()))
        );
        dest.write_all(&self.key)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use sphincsplus::SpxDomain;
    use strum::IntoEnumIterator;

    use crate::util::tmpfilename;

    /// A SLH-DSA-SHA2-128s key pair in Opentitan's Pre-Standardization RAW PEM format.
    const PRESTANDARD_PRIVATE_PEM: &str = "-----BEGIN RAW:SLH_DSA_SHA2_128s PRIVATE KEY-----\n\
        6bjY0UDbmzL4TnTVYwINqOCrxxyGNC8hJXMzKB9WDNfaSaVWNOfNyXSDc9opKeh2\n\
        dNVIlMTKhAWCYUnLhZ0gsw==\n\
        -----END RAW:SLH_DSA_SHA2_128s PRIVATE KEY-----\n";
    const PRESTANDARD_PUBLIC_PEM: &str = "-----BEGIN RAW:SLH_DSA_SHA2_128s PUBLIC KEY-----\n\
        2kmlVjTnzcl0g3PaKSnodnTVSJTEyoQFgmFJy4WdILM=\n\
        -----END RAW:SLH_DSA_SHA2_128s PUBLIC KEY-----\n";
    const SHA2_PUBLIC_HEX: &str =
        "da49a55634e7cdc9748373da2929e87674d54894c4ca8405826149cb859d20b3";

    #[test]
    fn test_pre_standard_pem_vectors() -> Result<()> {
        let public_key = load_spx_public_key_from_bytes(
            PRESTANDARD_PUBLIC_PEM.as_bytes(),
            SpxKeyLoadingMode::PublicOnly,
        )?;
        assert_eq!(public_key.algorithm(), SphincsPlus::Sha2128sSimple);
        assert_eq!(hex::encode(public_key.as_bytes()), SHA2_PUBLIC_HEX);

        let private_key = load_spx_private_key_from_bytes(PRESTANDARD_PRIVATE_PEM.as_bytes())?;
        assert_eq!(SpxPublicKey::from(&private_key), public_key);

        // We shouldn't be able to load the public key from the private key
        // unless the fallthrough option is enabled - in which case we should.
        assert!(
            load_spx_public_key_from_bytes(
                PRESTANDARD_PRIVATE_PEM.as_bytes(),
                SpxKeyLoadingMode::PublicOnly
            )
            .is_err()
        );
        assert_eq!(
            load_spx_public_key_from_bytes(
                PRESTANDARD_PRIVATE_PEM.as_bytes(),
                SpxKeyLoadingMode::Fallback
            )?,
            public_key
        );

        // Check that we can also use keys with `SPHINCS+` algorithm names instead of `SLH_DSA`.
        let sphincsplus =
            |pem: &str| pem.replace("RAW:SLH_DSA_SHA2_128s", "RAW:SPHINCS+_SHA2_128s_simple");
        assert_eq!(
            load_spx_public_key_from_bytes(
                sphincsplus(PRESTANDARD_PUBLIC_PEM).as_bytes(),
                SpxKeyLoadingMode::Fallback
            )?,
            public_key
        );
        assert_eq!(
            load_spx_private_key_from_bytes(sphincsplus(PRESTANDARD_PRIVATE_PEM).as_bytes())?,
            private_key
        );

        // A public key should never satisfy a request for a private key.
        assert!(load_spx_private_key_from_bytes(PRESTANDARD_PUBLIC_PEM.as_bytes()).is_err());
        Ok(())
    }

    /// A standard PKCS#8 / SPKI SLH-DSA-SHAKE-128s key pair encoded in both PEM and DER formats.
    const PKCS8_PRIVATE_PEM: &str = "-----BEGIN PRIVATE KEY-----\n\
        MFICAQAwCwYJYIZIAWUDBAMaBEB4i2IQNhIQvc97tjjHtV/b6ZrcuOg1Vn82LANY\n\
        QzQkhsxiHYkfzmmQt6u8AgCwa5IgqxgaKEjNtvbjc7wWDMFn\n\
        -----END PRIVATE KEY-----\n";
    const SPKI_PUBLIC_PEM: &str = "-----BEGIN PUBLIC KEY-----\n\
        MDAwCwYJYIZIAWUDBAMaAyEAzGIdiR/OaZC3q7wCALBrkiCrGBooSM229uNzvBYM\n\
        wWc=\n\
        -----END PUBLIC KEY-----\n";
    const PKCS8_PRIVATE_DER_HEX: &str = "3052020100300b060960864801650304031a0440788b6210361210bdcf7bb\
        638c7b55fdbe99adcb8e835567f362c035843342486cc621d891fce6990b7abbc0200b06b9220ab181a2848cdb6f6e\
        373bc160cc167";
    const SPKI_PUBLIC_DER_HEX: &str = "3030300b060960864801650304031a032100cc621d891fce6990b7abbc0200b\
        06b9220ab181a2848cdb6f6e373bc160cc167";
    const SHAKE2_PUBLIC_HEX: &str =
        "cc621d891fce6990b7abbc0200b06b9220ab181a2848cdb6f6e373bc160cc167";

    #[test]
    fn test_standard_pem_vectors() -> Result<()> {
        let public_key = load_spx_public_key_from_bytes(
            SPKI_PUBLIC_PEM.as_bytes(),
            SpxKeyLoadingMode::PublicOnly,
        )?;
        assert_eq!(public_key.algorithm(), SphincsPlus::Shake128sSimple);
        assert_eq!(hex::encode(public_key.as_bytes()), SHAKE2_PUBLIC_HEX);

        let private_key = load_spx_private_key_from_bytes(PKCS8_PRIVATE_PEM.as_bytes())?;
        assert_eq!(SpxPublicKey::from(&private_key), public_key);

        // We shouldn't be able to load the public key from the private key
        // unless the fallthrough option is enabled - in which case we should.
        assert!(
            load_spx_public_key_from_bytes(
                PKCS8_PRIVATE_PEM.as_bytes(),
                SpxKeyLoadingMode::PublicOnly
            )
            .is_err()
        );
        assert_eq!(
            load_spx_public_key_from_bytes(
                PKCS8_PRIVATE_PEM.as_bytes(),
                SpxKeyLoadingMode::Fallback
            )?,
            public_key
        );

        // A public key should never satisfy a request for a private key.
        assert!(load_spx_private_key_from_bytes(SPKI_PUBLIC_PEM.as_bytes()).is_err());
        Ok(())
    }

    #[test]
    fn test_standard_der_vectors() -> Result<()> {
        let spki_public_der = hex::decode(SPKI_PUBLIC_DER_HEX)?;
        let public_key =
            load_spx_public_key_from_bytes(&spki_public_der, SpxKeyLoadingMode::PublicOnly)?;
        assert_eq!(public_key.algorithm(), SphincsPlus::Shake128sSimple);
        assert_eq!(hex::encode(public_key.as_bytes()), SHAKE2_PUBLIC_HEX);

        let pkcs8_private_der = hex::decode(PKCS8_PRIVATE_DER_HEX)?;
        let private_key = load_spx_private_key_from_bytes(&pkcs8_private_der)?;
        assert_eq!(SpxPublicKey::from(&private_key), public_key);

        // We shouldn't be able to load the public key from the private key
        // unless the fallthrough option is enabled - in which case we should.
        assert!(
            load_spx_public_key_from_bytes(&pkcs8_private_der, SpxKeyLoadingMode::PublicOnly)
                .is_err()
        );
        assert_eq!(
            load_spx_public_key_from_bytes(&pkcs8_private_der, SpxKeyLoadingMode::Fallback)?,
            public_key
        );

        // A public key should never satisfy a request for a private key.
        assert!(load_spx_private_key_from_bytes(&spki_public_der).is_err());
        Ok(())
    }

    // Save -> Load roundtrip tests for every supported key format
    #[test]
    fn test_spx_format_roundtrip() -> Result<()> {
        for algorithm in [SphincsPlus::Shake128sSimple, SphincsPlus::Sha2128sSimple] {
            let (private_key, public_key) = SpxSecretKey::new_keypair(algorithm)?;

            for format in SpxKeyFormat::iter() {
                let private_path =
                    tmpfilename(&format!("test_private_{:?}.{}", algorithm, format.ext()));
                let public_path =
                    tmpfilename(&format!("test_public_{:?}.{}", algorithm, format.pub_ext()));

                save_spx_private_key(&private_key, &private_path, format)?;
                save_spx_public_key(&public_key, &public_path, format)?;

                let loaded_private_key = load_spx_private_key(&private_path)?;
                let loaded_public_key =
                    load_spx_public_key(&public_path, SpxKeyLoadingMode::PublicOnly)?;

                assert_eq!(loaded_private_key, private_key);
                assert_eq!(loaded_public_key, public_key);

                // Test extracting public key from private key file, with and without the fallback.
                assert!(load_spx_public_key(&private_path, SpxKeyLoadingMode::PublicOnly).is_err());
                let extracted_public_key =
                    load_spx_public_key(&private_path, SpxKeyLoadingMode::Fallback)?;
                assert_eq!(extracted_public_key, public_key);
            }
        }
        Ok(())
    }

    // [`SpxKeyFormat::PreStandardPem`] is tested in the `sphincsplus` implementation.
    // Do a very simple sign/verify smoketest with keys instead loaded from PKCS#8
    // formats to check that everything still works.
    #[test]
    fn test_pkcs8_sign_verify() -> Result<()> {
        let algorithm = SphincsPlus::Shake128sSimple;
        let (private_key, public_key) = SpxSecretKey::new_keypair(algorithm)?;

        let private_path = tmpfilename("test_pkcs8_private.der");
        let public_path = tmpfilename("test_pkcs8_public.der");

        save_spx_private_key(&private_key, &private_path, SpxKeyFormat::Pkcs8Der)?;
        save_spx_public_key(&public_key, &public_path, SpxKeyFormat::Pkcs8Der)?;

        let loaded_private_key = load_spx_private_key(&private_path)?;
        let loaded_public_key = load_spx_public_key(&public_path, SpxKeyLoadingMode::PublicOnly)?;

        let message = b"OpenTitan SLH-DSA PKCS#8 test message";
        let signature = loaded_private_key.sign(SpxDomain::Pure, message)?;
        loaded_public_key.verify(SpxDomain::Pure, &signature, message)?;
        Ok(())
    }

    // SLH-DSA keys stored as PEM-format PKCS#8/SPKI encoded objects that
    // contain RFC 9909 HashSLH-DSA OIDs. These keys are standard forms
    // that are recognized by e.g. `openssl asn1parse`.
    const HASH_SHA2_PKCS8_PRIVATE_PEM: &str = "-----BEGIN PRIVATE KEY-----\n\
    MFICAQAwCwYJYIZIAWUDBAMjBEBIjB3ttV/OvD4/9yf9LHHaYVECrox1YCuhMF8r\n\
    yHcCQmPlPkBjhfLuvc55qcfTg9r036qsYPgjUyPpQue7ertQ\n\
    -----END PRIVATE KEY-----\n";
    const HASH_SHA2_SPKI_PUBLIC_PEM: &str = "-----BEGIN PUBLIC KEY-----\n\
    MDAwCwYJYIZIAWUDBAMjAyEAY+U+QGOF8u69znmpx9OD2vTfqqxg+CNTI+lC57t6\n\
    u1A=\n\
    -----END PUBLIC KEY-----\n";
    const HASH_SHAKE_PKCS8_PRIVATE_PEM: &str = "-----BEGIN PRIVATE KEY-----\n\
    MFICAQAwCwYJYIZIAWUDBAMpBEBTh10ZwA4dsSd8FBx0MqPoVm7VTOwSmWtQd/Gv\n\
    5hKAck1mpOA63mf9xmxOsRCV50omE0OYXv2bqZCny/1W3qkb\n\
    -----END PRIVATE KEY-----\n";
    const HASH_SHAKE_SPKI_PUBLIC_PEM: &str = "-----BEGIN PUBLIC KEY-----\n\
    MDAwCwYJYIZIAWUDBAMpAyEATWak4DreZ/3GbE6xEJXnSiYTQ5he/ZupkKfL/Vbe\n\
    qRs=\n\
    -----END PUBLIC KEY-----\n";

    #[test]
    fn test_hash_slh_dsa_oids() -> Result<()> {
        // The HashSLH-DSA-SHA2-128S-WITH-SHA-256 OID in the Public Key (SPKI
        // object) case is handled by the fallback in SPHINCS+ parsing.
        assert!(
            load_spx_public_key_from_bytes(
                HASH_SHA2_SPKI_PUBLIC_PEM.as_bytes(),
                SpxKeyLoadingMode::PublicOnly,
            )
            .is_ok()
        );

        // FIXME: the other three HashSLH-DSA OIDs are not currently supported.
        assert!(
            load_spx_public_key_from_bytes(
                HASH_SHAKE_SPKI_PUBLIC_PEM.as_bytes(),
                SpxKeyLoadingMode::PublicOnly,
            )
            .is_err()
        );
        assert!(load_spx_private_key_from_bytes(HASH_SHA2_PKCS8_PRIVATE_PEM.as_bytes()).is_err());
        assert!(load_spx_private_key_from_bytes(HASH_SHAKE_PKCS8_PRIVATE_PEM.as_bytes()).is_err());
        Ok(())
    }
}
