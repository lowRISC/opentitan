// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;

use anyhow::{Context, Result, anyhow, bail, ensure};
use ml_dsa::pkcs8::der::asn1::OctetStringRef;
use ml_dsa::pkcs8::der::oid::db::fips204;
use ml_dsa::pkcs8::der::zeroize::Zeroizing;
use ml_dsa::pkcs8::der::{AnyRef, Decode, SliceReader, Tag, Tagged};
use ml_dsa::pkcs8::spki::AssociatedAlgorithmIdentifier;
use ml_dsa::pkcs8::{
    DecodePublicKey, EncodePrivateKey, EncodePublicKey, LineEnding, ObjectIdentifier,
    PrivateKeyInfoRef, SecretDocument, SubjectPublicKeyInfoRef,
};
use ml_dsa::{Keypair, MlDsaParams, Seed, SigningKey, VerifyingKey};
use strum::{Display, EnumString};

/// ML-DSA parameter sets with PKCS#8 / SubjectPublicKeyInfo support.
pub trait MldsaPkcs8Params:
    MlDsaParams + AssociatedAlgorithmIdentifier<Params = AnyRef<'static>>
{
}

impl<P> MldsaPkcs8Params for P where
    P: MlDsaParams + AssociatedAlgorithmIdentifier<Params = AnyRef<'static>>
{
}

/// ML-DSA parameter sets.
#[derive(Copy, Clone, PartialEq, Eq, Debug, EnumString, Display)]
#[strum(ascii_case_insensitive)]
pub enum MldsaParameterSet {
    #[strum(serialize = "ML-DSA-44")]
    Mldsa44,
    #[strum(serialize = "ML-DSA-65")]
    Mldsa65,
    #[strum(serialize = "ML-DSA-87")]
    Mldsa87,
}

impl MldsaParameterSet {
    /// Returns the parameter set with the given object identifier.
    pub fn from_oid(oid: ObjectIdentifier) -> Option<Self> {
        match oid {
            fips204::ID_ML_DSA_44 => Some(Self::Mldsa44),
            fips204::ID_ML_DSA_65 => Some(Self::Mldsa65),
            fips204::ID_ML_DSA_87 => Some(Self::Mldsa87),
            _ => None,
        }
    }
}

/// Formats that can be used to represent ML-DSA keys: PKCS#8 for private keys,
/// and `SubjectPublicKeyInfo` for public keys.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, EnumString, Display)]
#[strum(ascii_case_insensitive)]
pub enum MldsaKeyFormat {
    #[default]
    #[strum(to_string = "pem", serialize = "pkcs8-pem")]
    Pem,
    #[strum(to_string = "der", serialize = "pkcs8-der")]
    Der,
}

impl MldsaKeyFormat {
    /// Standard file extension for a private key in this format.
    pub fn ext(&self) -> &'static str {
        match self {
            Self::Pem => "pem",
            Self::Der => "der",
        }
    }

    /// Standard file extension for a public key in this format.
    pub fn pub_ext(&self) -> String {
        format!("pub.{}", self.ext())
    }
}

/// Decodes a PEM or DER encoded key into its DER encoding.
fn decode_key(input: &[u8]) -> Result<SecretDocument> {
    if input.trim_ascii_start().starts_with(b"-----BEGIN") {
        let pem = std::str::from_utf8(input).context("Failed to read PEM contents as UTF-8")?;
        Ok(SecretDocument::from_pem(pem)?.1)
    } else {
        Ok(SecretDocument::try_from(input)?)
    }
}

/// Reads a PEM or DER encoded key file into its DER encoding.
pub fn read_mldsa_key_file(path: impl AsRef<Path>) -> Result<SecretDocument> {
    let path = path.as_ref();
    let data = Zeroizing::new(
        std::fs::read(path).with_context(|| format!("Failed to read file: {path:?}"))?,
    );
    decode_key(&data)
}

/// Decodes the seed + expanded form of an ML-DSA private key.
fn signing_key_from_seed_and_expanded<P: MldsaPkcs8Params>(
    private_key: &[u8],
) -> Result<SigningKey<P>> {
    let (seed, expanded) = AnyRef::from_der(private_key)?.sequence(|r: &mut SliceReader<'_>| {
        Ok::<_, ml_dsa::pkcs8::der::Error>((
            <&OctetStringRef>::decode(r)?.as_bytes(),
            <&OctetStringRef>::decode(r)?.as_bytes(),
        ))
    })?;
    let seed = Zeroizing::new(
        Seed::try_from(seed).map_err(|_| anyhow!("Bad ML-DSA seed length {}", seed.len()))?,
    );
    let key = SigningKey::<P>::from_seed(&seed);
    // The ml-dsa crate doesn't natively support the seed + expanded form, instead encouraging
    // use of the seed form, and so marks this functionality as deprecated. If a future crate
    // version drops this function, this check should probably be dropped.
    #[allow(deprecated)]
    let derived = Zeroizing::new(key.expanded_key().to_expanded());
    ensure!(
        derived.as_slice() == expanded,
        "ML-DSA expanded private key does not match the seed"
    );
    Ok(key)
}

/// Decodes an ML-DSA private key from a PKCS#8v1 (PrivateKeyInfo) or PKCS#8v2
/// (OneAsymmetricKey) in the seed or seed + expanded form.
fn signing_key_from_pkcs8<P: MldsaPkcs8Params>(
    info: PrivateKeyInfoRef<'_>,
) -> Result<SigningKey<P>> {
    info.algorithm
        .assert_algorithm_oid(P::ALGORITHM_IDENTIFIER.oid)?;
    let private_key = info.private_key.as_bytes();
    let key = match AnyRef::from_der(private_key)?.tag() {
        Tag::Sequence => signing_key_from_seed_and_expanded::<P>(private_key)?,
        Tag::OctetString => bail!("Expanded-only ML-DSA private keys are not supported"),
        _ => SigningKey::<P>::try_from(info.clone())?,
    };
    if let Some(public_key) = &info.public_key {
        ensure!(
            public_key.as_bytes() == Some(key.verifying_key().encode().as_slice()),
            "ML-DSA public key does not match the private key"
        );
    }
    Ok(key)
}

/// Load an ML-DSA private key from its PEM or DER encoded PKCS#8 bytes.
pub fn mldsa_private_key_from_bytes<P: MldsaPkcs8Params>(input: &[u8]) -> Result<SigningKey<P>> {
    let doc = decode_key(input)?;
    signing_key_from_pkcs8(PrivateKeyInfoRef::from_der(doc.as_bytes())?)
}

/// Load an ML-DSA private key from a PEM or DER file.
pub fn load_mldsa_private_key<P: MldsaPkcs8Params>(
    path: impl AsRef<Path>,
) -> Result<SigningKey<P>> {
    let doc = read_mldsa_key_file(path)?;
    signing_key_from_pkcs8(PrivateKeyInfoRef::from_der(doc.as_bytes())?)
}

/// Write an ML-DSA private key (seed form) to a file in the given format.
pub fn save_mldsa_private_key<P: MldsaPkcs8Params>(
    key: &SigningKey<P>,
    path: impl AsRef<Path>,
    format: MldsaKeyFormat,
) -> Result<()> {
    let path = path.as_ref();
    match format {
        MldsaKeyFormat::Pem => std::fs::write(path, key.to_pkcs8_pem(LineEnding::default())?),
        MldsaKeyFormat::Der => std::fs::write(path, key.to_pkcs8_der()?.as_bytes()),
    }
    .with_context(|| format!("Failed to write file: {path:?}"))
}

/// Load an ML-DSA public key from its PEM or DER encoded SubjectPublicKeyInfo bytes.
pub fn mldsa_public_key_from_bytes<P: MldsaPkcs8Params>(input: &[u8]) -> Result<VerifyingKey<P>> {
    Ok(VerifyingKey::from_public_key_der(
        decode_key(input)?.as_bytes(),
    )?)
}

/// Load an ML-DSA public key from a PEM or DER file.
pub fn load_mldsa_public_key<P: MldsaPkcs8Params>(
    path: impl AsRef<Path>,
) -> Result<VerifyingKey<P>> {
    Ok(VerifyingKey::from_public_key_der(
        read_mldsa_key_file(path)?.as_bytes(),
    )?)
}

/// Decodes the DER encoding of an ML-DSA public key (SubjectPublicKeyInfo)
/// or private key (PKCS#8), returning the public key and, for a private key,
/// the private key.
pub fn mldsa_key_from_der<P: MldsaPkcs8Params>(
    der: &[u8],
) -> Result<(VerifyingKey<P>, Option<SigningKey<P>>)> {
    // Pick the decoder by structure so that its errors are not masked by
    // the other one.
    if let Ok(spki) = SubjectPublicKeyInfoRef::from_der(der) {
        return Ok((VerifyingKey::try_from(spki)?, None));
    }
    let info = PrivateKeyInfoRef::from_der(der)
        .context("Not an ML-DSA public (SubjectPublicKeyInfo) or private (PKCS#8) key")?;
    let key = signing_key_from_pkcs8(info)?;
    Ok((key.verifying_key(), Some(key)))
}

/// Load an ML-DSA public or private key from a PEM or DER file, returning the
/// public key and, for a private key file, the private key.
pub fn load_mldsa_key<P: MldsaPkcs8Params>(
    path: impl AsRef<Path>,
) -> Result<(VerifyingKey<P>, Option<SigningKey<P>>)> {
    mldsa_key_from_der(read_mldsa_key_file(path)?.as_bytes())
}

/// Write an ML-DSA public key to a file in the given format.
pub fn save_mldsa_public_key<P: MldsaPkcs8Params>(
    key: &VerifyingKey<P>,
    path: impl AsRef<Path>,
    format: MldsaKeyFormat,
) -> Result<()> {
    let path = path.as_ref();
    match format {
        MldsaKeyFormat::Pem => std::fs::write(path, key.to_public_key_pem(LineEnding::default())?),
        MldsaKeyFormat::Der => std::fs::write(path, key.to_public_key_der()?.as_bytes()),
    }
    .with_context(|| format!("Failed to write file: {path:?}"))
}

/// Returns the parameter set of the DER encoding of an ML-DSA public or private key.
pub fn mldsa_parameter_set_from_der(der: &[u8]) -> Result<MldsaParameterSet> {
    let oid = match SubjectPublicKeyInfoRef::from_der(der) {
        Ok(spki) => spki.algorithm.oid,
        Err(_) => PrivateKeyInfoRef::from_der(der)?.algorithm.oid,
    };
    MldsaParameterSet::from_oid(oid).ok_or_else(|| anyhow!("Not an ML-DSA key: {oid}"))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::util::testdata;
    use ml_dsa::pkcs8::der::Encode;
    use ml_dsa::pkcs8::der::asn1::BitStringRef;
    use ml_dsa::{Generate, MlDsa65, MlDsa87};

    #[test]
    fn key_encoding() -> Result<()> {
        let sk = SigningKey::<MlDsa87>::try_generate()?;
        let pk = sk.verifying_key();
        let pem = sk.to_pkcs8_pem(LineEnding::default())?;
        assert_eq!(mldsa_private_key_from_bytes::<MlDsa87>(pem.as_bytes())?, sk);
        let der = sk.to_pkcs8_der()?;
        assert_eq!(mldsa_private_key_from_bytes::<MlDsa87>(der.as_bytes())?, sk);
        let pem = pk.to_public_key_pem(LineEnding::default())?;
        assert_eq!(mldsa_public_key_from_bytes::<MlDsa87>(pem.as_bytes())?, pk);
        let der = pk.to_public_key_der()?;
        assert_eq!(mldsa_public_key_from_bytes::<MlDsa87>(der.as_bytes())?, pk);

        // A private key cannot be loaded as a public key and vice versa.
        assert!(mldsa_private_key_from_bytes::<MlDsa87>(der.as_bytes()).is_err());
        let der = sk.to_pkcs8_der()?;
        assert!(mldsa_public_key_from_bytes::<MlDsa87>(der.as_bytes()).is_err());
        // The parameter set must match.
        assert!(mldsa_private_key_from_bytes::<MlDsa65>(der.as_bytes()).is_err());
        Ok(())
    }

    /// Encodes `sk` as a PKCS#8v2 (OneAsymmetricKey) containing `pk`.
    fn to_pkcs8_v2(sk: &SigningKey<MlDsa87>, pk: &VerifyingKey<MlDsa87>) -> Result<Vec<u8>> {
        let v1 = sk.to_pkcs8_der()?;
        let mut info = PrivateKeyInfoRef::from_der(v1.as_bytes())?;
        let pk = pk.encode();
        info.public_key = Some(BitStringRef::new(0, &pk)?);
        Ok(info.to_der()?)
    }

    #[test]
    fn pkcs8_v2() -> Result<()> {
        let sk = SigningKey::<MlDsa87>::try_generate()?;
        let v2 = to_pkcs8_v2(&sk, &sk.verifying_key())?;
        assert_eq!(mldsa_private_key_from_bytes::<MlDsa87>(&v2)?, sk);

        // The public key must match the private key.
        let other = SigningKey::<MlDsa87>::try_generate()?;
        let v2 = to_pkcs8_v2(&sk, &other.verifying_key())?;
        assert!(mldsa_private_key_from_bytes::<MlDsa87>(&v2).is_err());
        // The consistency error is reported when loading a key of unknown kind.
        let err = mldsa_key_from_der::<MlDsa87>(&v2).unwrap_err();
        assert!(err.to_string().contains("does not match the private key"));
        Ok(())
    }

    #[test]
    fn parameter_set() {
        let oid = MlDsa87::ALGORITHM_IDENTIFIER.oid;
        assert_eq!(
            MldsaParameterSet::from_oid(oid),
            Some(MldsaParameterSet::Mldsa87)
        );
        assert_eq!(
            "ml-dsa-87".parse::<MldsaParameterSet>(),
            Ok(MldsaParameterSet::Mldsa87)
        );
    }

    #[test]
    fn openssl_interop() -> Result<()> {
        // Private keys generated with OpenSSL 3.5 in its three output formats.
        let seed_priv = std::fs::read(testdata("mldsa/openssl_mldsa87.seed-priv.pem"))?;
        let seed_only = std::fs::read_to_string(testdata("mldsa/openssl_mldsa87.seed-only.pem"))?;
        let priv_only = std::fs::read(testdata("mldsa/openssl_mldsa87.priv-only.pem"))?;
        let public = std::fs::read(testdata("mldsa/openssl_mldsa87.pub.pem"))?;

        let pk = mldsa_public_key_from_bytes::<MlDsa87>(&public)?;
        let both = mldsa_private_key_from_bytes::<MlDsa87>(&seed_priv)?;
        let seed = mldsa_private_key_from_bytes::<MlDsa87>(seed_only.as_bytes())?;
        assert_eq!(both, seed);
        assert_eq!(seed.verifying_key(), pk);
        assert_eq!(
            *seed.to_pkcs8_pem(LineEnding::LF)?,
            seed_only.replace("\r\n", "\n")
        );
        let err = mldsa_private_key_from_bytes::<MlDsa87>(&priv_only).unwrap_err();
        assert!(err.to_string().contains("Expanded-only"));
        Ok(())
    }
}
