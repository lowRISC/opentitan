//! CBOR encoding and decoding of a [`PublicKey`].

use crate::publickey::{EcKind, KeyAgreementPublicKey, PublicKey, SignatureKind};
use anyhow::{anyhow, bail, ensure, Context, Result};
use coset::cbor::value::Value;
use coset::iana::{self, EnumI64};
use coset::{Algorithm, CoseKey, CoseKeyBuilder, CoseSign1, KeyOperation, KeyType, Label};
use openssl::bn::{BigNum, BigNumContext};
use openssl::ec::{EcGroup, EcKey};
use openssl::ecdsa::EcdsaSig;
use openssl::nid::Nid;
use openssl::pkey::{Id, PKey, Public};
use std::collections::HashSet;

impl PublicKey {
    /// Create a public key from a [`CoseKey`].
    pub fn from_cose_key(cose_key: &CoseKey) -> Result<Self> {
        if !cose_key.key_ops.is_empty() {
            ensure!(cose_key.key_ops.contains(&KeyOperation::Assigned(iana::KeyOperation::Verify)));
        }
        let pkey = to_pkey(cose_key)?;
        pkey.try_into().context("Making PublicKey from PKey")
    }

    /// Verifies a COSE_Sign1 signature over its message. This function handles the conversion of
    /// the signature format that is needed for some algorithms.
    pub fn verify_cose_sign1(&self, sign1: &CoseSign1, aad: &[u8]) -> Result<()> {
        ensure!(sign1.protected.header.crit.is_empty(), "No critical headers allowed");
        ensure!(
            sign1.protected.header.alg == Some(Algorithm::Assigned(iana_algorithm(self.kind()))),
            "Algorithm mistmatch in protected header. \
             Signature - protected.header.alg: {:?}, Key - kind: {:?}",
            sign1.protected.header.alg,
            iana_algorithm(self.kind())
        );
        sign1.verify_signature(aad, |signature, message| match self.kind() {
            SignatureKind::Ec(_) => {
                let der =
                    ec_cose_signature_to_der(self.kind(), signature).context("Signature to DER")?;
                self.verify(&der, message)
            }
            _ => self.verify(signature, message),
        })
    }

    /// Convert the public key into a [`CoseKey`].
    pub fn to_cose_key(&self) -> Result<CoseKey> {
        let builder = match self.kind() {
            SignatureKind::Ed25519 => {
                let label_crv = iana::OkpKeyParameter::Crv.to_i64();
                let label_x = iana::OkpKeyParameter::X.to_i64();
                let x = self.pkey().raw_public_key().context("Get ed25519 raw public key")?;
                CoseKeyBuilder::new_okp_key()
                    .param(label_crv, Value::from(iana::EllipticCurve::Ed25519.to_i64()))
                    .param(label_x, Value::from(x))
            }
            SignatureKind::Ec(ec) => {
                let key = self.pkey().ec_key().unwrap();
                let group = key.group();
                let mut ctx = BigNumContext::new().context("Failed to create bignum context")?;
                let mut x = BigNum::new().context("Failed to create x coord")?;
                let mut y = BigNum::new().context("Failed to create y coord")?;
                key.public_key()
                    .affine_coordinates_gfp(group, &mut x, &mut y, &mut ctx)
                    .context("Get EC coordinates")?;
                let (crv, coord_len) = match ec {
                    EcKind::P256 => (iana::EllipticCurve::P_256, 32),
                    EcKind::P384 => (iana::EllipticCurve::P_384, 48),
                };

                let x = adjust_coord(x.to_vec(), coord_len)?;
                let y = adjust_coord(y.to_vec(), coord_len)?;
                CoseKeyBuilder::new_ec2_pub_key(crv, x, y)
            }
        };
        Ok(builder
            .algorithm(iana_algorithm(self.kind()))
            .add_key_op(iana::KeyOperation::Verify)
            .build())
    }
}

impl KeyAgreementPublicKey {
    pub(super) fn from_cose_key(cose_key: &CoseKey) -> Result<Self> {
        // RFC 9052 says the key_op for derive key is only for private keys. The public key
        // has no key_ops (see Appendix B for an example).
        ensure!(cose_key.key_ops.is_empty());
        let pkey = to_pkey(cose_key)?;
        pkey.try_into().context("Making KeyAgreementPublicKey from PKey")
    }
}

fn to_pkey(cose_key: &CoseKey) -> Result<PKey<Public>> {
    match cose_key.kty {
        KeyType::Assigned(iana::KeyType::OKP) => Ok(pkey_from_okp_key(cose_key)?),
        KeyType::Assigned(iana::KeyType::EC2) => Ok(pkey_from_ec2_key(cose_key)?),
        _ => bail!("Unexpected KeyType value: {:?}", cose_key.kty),
    }
}

fn adjust_coord(mut coordinate: Vec<u8>, length: usize) -> Result<Vec<u8>> {
    // Use loops "just in case". However we should never see a coordinate with more than one
    // extra leading byte. The chances of more than one trailing byte is also quite small --
    // roughly 1/65000.
    while coordinate.len() > length {
        ensure!(coordinate[0] == 0, "unexpected non-zero leading byte on public key");
        coordinate.remove(0);
    }

    while coordinate.len() < length {
        coordinate.insert(0, 0);
    }

    Ok(coordinate)
}

fn pkey_from_okp_key(cose_key: &CoseKey) -> Result<PKey<Public>> {
    ensure!(cose_key.kty == KeyType::Assigned(iana::KeyType::OKP));
    ensure!(
        cose_key.alg == Some(Algorithm::Assigned(iana::Algorithm::EdDSA))
            || cose_key.alg == Some(Algorithm::Assigned(iana::Algorithm::ECDH_ES_HKDF_256))
    );
    ensure_no_disallowed_labels(cose_key)?;
    let crv = get_label_value(cose_key, Label::Int(iana::OkpKeyParameter::Crv.to_i64()))?;
    let x = get_label_value_as_bytes(cose_key, Label::Int(iana::OkpKeyParameter::X.to_i64()))?;
    let curve_id = if crv == &Value::from(iana::EllipticCurve::Ed25519.to_i64()) {
        Id::ED25519
    } else if crv == &Value::from(iana::EllipticCurve::X25519.to_i64()) {
        Id::X25519
    } else {
        bail!("Given crv is invalid: '{crv:?}'");
    };
    PKey::public_key_from_raw_bytes(x, curve_id).context("Failed to instantiate key")
}

fn pkey_from_ec2_key(cose_key: &CoseKey) -> Result<PKey<Public>> {
    ensure!(cose_key.kty == KeyType::Assigned(iana::KeyType::EC2));
    ensure_no_disallowed_labels(cose_key)?;
    let crv = get_label_value(cose_key, Label::Int(iana::Ec2KeyParameter::Crv.to_i64()))?;
    let x = get_label_value_as_bytes(cose_key, Label::Int(iana::Ec2KeyParameter::X.to_i64()))?;
    let y = get_label_value_as_bytes(cose_key, Label::Int(iana::Ec2KeyParameter::Y.to_i64()))?;
    match cose_key.alg {
        Some(Algorithm::Assigned(iana::Algorithm::ES256))
        | Some(Algorithm::Assigned(iana::Algorithm::ECDH_ES_HKDF_256)) => {
            ensure!(crv == &Value::from(iana::EllipticCurve::P_256.to_i64()));
            pkey_from_ec_coords(Nid::X9_62_PRIME256V1, x, y).context("Failed to instantiate key")
        }
        Some(Algorithm::Assigned(iana::Algorithm::ES384)) => {
            ensure!(crv == &Value::from(iana::EllipticCurve::P_384.to_i64()));
            pkey_from_ec_coords(Nid::SECP384R1, x, y).context("Failed to instantiate key")
        }
        _ => bail!("Need to specify ES256 or ES384 key algorithm. Got {:?}", cose_key.alg),
    }
}

fn pkey_from_ec_coords(nid: Nid, x: &[u8], y: &[u8]) -> Result<PKey<Public>> {
    let group = EcGroup::from_curve_name(nid).context("Failed to construct curve group")?;
    let x = BigNum::from_slice(x).context("Failed to create x coord")?;
    let y = BigNum::from_slice(y).context("Failed to create y coord")?;
    let key = EcKey::from_public_key_affine_coordinates(&group, &x, &y)
        .context("Failed to create EC public key")?;
    PKey::from_ec_key(key).context("Failed to create PKey")
}

fn ensure_no_disallowed_labels(cose_key: &CoseKey) -> Result<()> {
    let allow_list = match cose_key.kty {
        KeyType::Assigned(iana::KeyType::EC2) => HashSet::from([
            iana::Ec2KeyParameter::Crv.to_i64(),
            iana::Ec2KeyParameter::X.to_i64(),
            iana::Ec2KeyParameter::Y.to_i64(),
        ]),
        KeyType::Assigned(iana::KeyType::OKP) => {
            HashSet::from([iana::OkpKeyParameter::Crv.to_i64(), iana::OkpKeyParameter::X.to_i64()])
        }
        _ => bail!("Invalid key type in COSE key"),
    };

    let params = cose_key.params.clone();
    let disallowed: Vec<(Label, String)> = params
        .into_iter()
        .filter(|(label, _)| match label {
            Label::Int(int) => !allow_list.contains(int),
            Label::Text(_) => true,
        })
        .map(|(label, value)| -> (Label, String) {
            let string = match value.as_bytes() {
                Some(bytes) => hex::encode(bytes),
                None => String::from("Expected Bytes, got {value:?}"),
            };
            (label, string)
        })
        .collect();

    ensure!(disallowed.is_empty(), "disallowed labels should be empty: {:?}", disallowed);

    Ok(())
}

/// Get the value corresponding to the provided label within the supplied CoseKey or error if it's
/// not present.
fn get_label_value(key: &CoseKey, label: Label) -> Result<&Value> {
    Ok(&key
        .params
        .iter()
        .find(|(k, _)| k == &label)
        .ok_or_else(|| anyhow!("Label {:?} not found", label))?
        .1)
}

/// Get the byte string for the corresponding label within the key if the label exists and the
/// value is actually a byte array.
fn get_label_value_as_bytes(key: &CoseKey, label: Label) -> Result<&[u8]> {
    get_label_value(key, label)?
        .as_bytes()
        .ok_or_else(|| anyhow!("Value not a bstr."))
        .map(Vec::as_slice)
}

fn ec_cose_signature_to_der(kind: SignatureKind, signature: &[u8]) -> Result<Vec<u8>> {
    let coord_len = ec_coord_len(kind);
    ensure!(signature.len() == coord_len * 2, "Unexpected signature length");
    let r = BigNum::from_slice(&signature[..coord_len]).context("Creating BigNum for r")?;
    let s = BigNum::from_slice(&signature[coord_len..]).context("Creating BigNum for s")?;
    let signature = EcdsaSig::from_private_components(r, s).context("Creating ECDSA signature")?;
    signature.to_der().context("Failed to DER encode signature")
}

fn ec_coord_len(kind: SignatureKind) -> usize {
    match kind {
        SignatureKind::Ec(kind) => match kind {
            EcKind::P256 => 32,
            EcKind::P384 => 48,
        },
        SignatureKind::Ed25519 => 32,
    }
}

fn iana_algorithm(kind: SignatureKind) -> iana::Algorithm {
    match kind {
        SignatureKind::Ed25519 => iana::Algorithm::EdDSA,
        SignatureKind::Ec(EcKind::P256) => iana::Algorithm::ES256,
        SignatureKind::Ec(EcKind::P384) => iana::Algorithm::ES384,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::publickey::testkeys::{
        PrivateKey, EC2_KEY_WITH_HIGH_BITS_SET_PEM, EC2_KEY_WITH_LEADING_ZEROS_PEM,
        ED25519_KEY_PEM, ED25519_KEY_WITH_LEADING_ZEROS_PEM, P256_KEY_PEM,
    };
    use coset::{CoseSign1Builder, HeaderBuilder};
    use std::collections::HashSet;

    impl PrivateKey {
        pub(in crate::cbor) fn sign_cose_sign1(&self, payload: Vec<u8>) -> CoseSign1 {
            CoseSign1Builder::new()
                .protected(HeaderBuilder::new().algorithm(iana_algorithm(self.kind())).build())
                .payload(payload)
                .create_signature(b"", |m| {
                    let signature = self.sign(m).unwrap();
                    match self.kind() {
                        SignatureKind::Ec(_) => ec_der_signature_to_cose(self.kind(), &signature),
                        _ => signature,
                    }
                })
                .build()
        }
    }

    fn ec_der_signature_to_cose(kind: SignatureKind, signature: &[u8]) -> Vec<u8> {
        let coord_len = ec_coord_len(kind);
        let signature = EcdsaSig::from_der(signature).unwrap();
        let mut r = signature.r().to_vec_padded(coord_len.try_into().unwrap()).unwrap();
        let mut s = signature.s().to_vec_padded(coord_len.try_into().unwrap()).unwrap();
        r.append(&mut s);
        r
    }

    fn sign_and_verify(pem: &str) {
        let key = PrivateKey::from_pem(pem);
        let sign1 = key.sign_cose_sign1(b"signed payload".to_vec());
        key.public_key().verify_cose_sign1(&sign1, b"").unwrap();
    }

    #[test]
    fn sign_and_verify_okp() {
        sign_and_verify(ED25519_KEY_PEM[0])
    }

    #[test]
    fn sign_and_verify_ec2() {
        sign_and_verify(P256_KEY_PEM[0])
    }

    #[test]
    fn verify_cose_sign1() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]);
        let sign1 = CoseSign1Builder::new()
            .protected(HeaderBuilder::new().algorithm(iana::Algorithm::EdDSA).build())
            .payload(b"the message".to_vec())
            .create_signature(b"the aad", |m| key.sign(m).unwrap())
            .build();
        key.public_key().verify_cose_sign1(&sign1, b"the aad").unwrap();
    }

    #[test]
    fn verify_cose_sign1_fails_with_wrong_aad() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]);
        let sign1 = CoseSign1Builder::new()
            .protected(HeaderBuilder::new().algorithm(iana::Algorithm::ES256).build())
            .payload(b"the message".to_vec())
            .create_signature(b"correct aad", |m| key.sign(m).unwrap())
            .build();
        key.public_key().verify_cose_sign1(&sign1, b"bad").unwrap_err();
    }

    #[test]
    fn verify_cose_sign1_fails_with_wrong_algorithm() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]);
        let sign1 = CoseSign1Builder::new()
            .protected(HeaderBuilder::new().algorithm(iana::Algorithm::ES256).build())
            .payload(b"the message".to_vec())
            .create_signature(b"", |m| key.sign(m).unwrap())
            .build();
        key.public_key().verify_cose_sign1(&sign1, b"").unwrap_err();
    }

    #[test]
    fn verify_cose_sign1_with_non_crit_header() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]);
        let sign1 = CoseSign1Builder::new()
            .protected(
                HeaderBuilder::new()
                    .algorithm(iana::Algorithm::EdDSA)
                    .value(1000, Value::from(2000))
                    .build(),
            )
            .payload(b"the message".to_vec())
            .create_signature(b"", |m| key.sign(m).unwrap())
            .build();
        key.public_key().verify_cose_sign1(&sign1, b"").unwrap()
    }

    #[test]
    fn verify_cose_sign1_fails_with_crit_header() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]);
        let sign1 = CoseSign1Builder::new()
            .protected(
                HeaderBuilder::new()
                    .algorithm(iana::Algorithm::EdDSA)
                    .add_critical(iana::HeaderParameter::Alg)
                    .build(),
            )
            .payload(b"the message".to_vec())
            .create_signature(b"", |m| key.sign(m).unwrap())
            .build();
        key.public_key().verify_cose_sign1(&sign1, b"").unwrap_err();
    }

    fn to_and_from_cose_key(pem: &str) {
        let key = PrivateKey::from_pem(pem).public_key();
        let value = key.to_cose_key().unwrap();
        let new_key = PublicKey::from_cose_key(&value).unwrap();
        assert!(key.pkey().public_eq(new_key.pkey()));
    }
    #[test]
    fn to_and_from_okp_cose_key() {
        to_and_from_cose_key(ED25519_KEY_PEM[0]);
    }

    #[test]
    fn to_and_from_ec2_cose_key() {
        to_and_from_cose_key(P256_KEY_PEM[0]);
    }

    #[test]
    fn from_ed25519_pkey_with_leading_zeros() {
        for pem in ED25519_KEY_WITH_LEADING_ZEROS_PEM {
            let key = PrivateKey::from_pem(pem).public_key();
            let cose_key = key.to_cose_key().unwrap();
            let kind = key.kind();
            assert_eq!(kind, SignatureKind::Ed25519);
            let expected_size = ec_coord_len(kind);
            let x =
                get_label_value_as_bytes(&cose_key, Label::Int(iana::OkpKeyParameter::X.to_i64()))
                    .unwrap();
            assert_eq!(x.len(), expected_size, "X coordinate is the wrong size\n{}", pem);
            assert_eq!(x[0], 0);
        }
    }

    fn check_coordinate_lengths_and_first_byte(
        pems: &[&str],
        first_byte_check: fn(&[u8], &[u8]) -> bool,
    ) {
        let mut curves = HashSet::new();
        for pem in pems {
            let key = PrivateKey::from_pem(pem).public_key();
            let cose_key = key.to_cose_key().unwrap();
            let kind = key.kind();
            match kind {
                SignatureKind::Ec(inner) => {
                    curves.insert(inner);
                }
                SignatureKind::Ed25519 => panic!("signature kind should not be ED25519"),
            };
            let expected_size = ec_coord_len(kind);
            let x =
                get_label_value_as_bytes(&cose_key, Label::Int(iana::Ec2KeyParameter::X.to_i64()))
                    .unwrap();
            assert_eq!(x.len(), expected_size, "X coordinate is the wrong size\n{}", pem);

            let y =
                get_label_value_as_bytes(&cose_key, Label::Int(iana::Ec2KeyParameter::Y.to_i64()))
                    .unwrap();
            assert_eq!(y.len(), expected_size, "Y coordinate is the wrong size\n{}", pem);
            assert!(first_byte_check(x, y));
        }
        assert!(curves.contains(&EcKind::P256));
        assert!(curves.contains(&EcKind::P384));
    }

    #[test]
    fn from_ec2_pkey_with_leading_zeros() {
        fn check(x: &[u8], y: &[u8]) -> bool {
            x[0] == 0 || y[0] == 0
        }
        check_coordinate_lengths_and_first_byte(EC2_KEY_WITH_LEADING_ZEROS_PEM, check)
    }

    #[test]
    fn from_ec2_pkey_with_high_bits_set() {
        fn check(x: &[u8], y: &[u8]) -> bool {
            (x[0] & 0x80 == 0x80) && (y[0] & 0x80 == 0x80)
        }
        check_coordinate_lengths_and_first_byte(EC2_KEY_WITH_HIGH_BITS_SET_PEM, check)
    }
}
