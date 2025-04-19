use std::collections::HashMap;

use crate::cbor::field_value::FieldValue;
use crate::cbor::{canonicalize_map, serialize, value_from_bytes};
use crate::dice::ChainForm;
use crate::rkp::{Csr, CsrPayload, DeviceInfo, DeviceInfoVersion, KeysToSign, ProtectedData};
use crate::session::{RkpInstance, Session};
use anyhow::{anyhow, bail, ensure, Context, Result};
use base64::{prelude::BASE64_STANDARD, Engine};
use ciborium::value::Value;
use coset::{AsCborValue, CoseKey};
use openssl::pkey::Id;
use openssl::stack::Stack;
use openssl::x509::store::X509StoreBuilder;
use openssl::x509::verify::X509VerifyFlags;
use openssl::x509::{X509StoreContext, X509};

const VERSION_OR_DEVICE_INFO_INDEX: usize = 0;

impl KeysToSign {
    pub(crate) fn from_bytes(buffer: &[u8]) -> Result<Self> {
        let value = value_from_bytes(buffer)?;
        let field_value = FieldValue::from_value("KeysToSign", value);
        Self::from_value(field_value)
    }
    fn from_value(value: FieldValue) -> Result<KeysToSign> {
        Ok(KeysToSign(
            value.into_array()?.into_iter().map(|v| CoseKey::from_cbor_value(v).unwrap()).collect(),
        ))
    }
}

impl CsrPayload {
    fn from_value(value: &Value, session: &Session) -> Result<Self> {
        let serialized = match value.clone().into_bytes() {
            Ok(bytes) => bytes,
            Err(_) => bail!("CsrPayload had no bytes"),
        };

        let mut csr_payload = match value_from_bytes(serialized.as_slice())? {
            Value::Array(a) => a,
            other => bail!("CsrPayload is expected to be an array, found {other:?}"),
        };

        let keys_to_sign = FieldValue::from_optional_value("KeysToSign", csr_payload.pop());
        let device_info = FieldValue::from_optional_value("DeviceInfo", csr_payload.pop());
        let certificate_type =
            FieldValue::from_optional_value("CertificateType", csr_payload.pop());
        let version = FieldValue::from_optional_value("Version", csr_payload.pop()).into_u64()?;
        if version != 3 {
            bail!("Invalid CsrPayload version. Only '3' is supported");
        }

        let certificate_type = certificate_type.into_string()?;

        const CERTIFICATE_TYPE_RKPVM: &str = "rkp-vm";
        match session.options.rkp_instance {
            RkpInstance::Avf => ensure!(
                CERTIFICATE_TYPE_RKPVM == certificate_type,
                "CertificateType must be 'rkp-vm' for AVF"
            ),
            _ => ensure!(
                CERTIFICATE_TYPE_RKPVM != certificate_type,
                "CertificateType must not be 'rkp-vm' for non-AVF"
            ),
        }

        let device_info = DeviceInfo::from_cbor_values(
            device_info.into_map()?,
            Some(DeviceInfoVersion::V3),
            session.options.is_factory,
        )?;
        let keys_to_sign = KeysToSign::from_value(keys_to_sign)?;

        Ok(CsrPayload { serialized, certificate_type, device_info, keys_to_sign })
    }
}

impl Csr {
    /// Parse base64-encoded CBOR data as a Certificate Signing Request.
    pub fn from_base64_cbor<S: AsRef<[u8]>>(session: &Session, base64: &S) -> Result<Self> {
        let cbor: Vec<u8> = BASE64_STANDARD.decode(base64).context("invalid base64 CSR")?;
        Self::from_cbor(session, cbor.as_slice())
    }

    /// Read and parse CBOR data as a Certificate Signing Request.
    pub fn from_cbor<S: std::io::Read>(session: &Session, cbor: S) -> Result<Self> {
        let value: Value = ciborium::de::from_reader(cbor).context("invalid CBOR")?;
        let mut array = match value {
            Value::Array(a) if a.is_empty() => bail!("CSR CBOR is an empty array"),
            Value::Array(a) => a,
            other => bail!("expected array, found {other:?}"),
        };
        let version_or_device_info =
            std::mem::replace(&mut array[VERSION_OR_DEVICE_INFO_INDEX], Value::Null);
        match version_or_device_info {
            Value::Array(device_info) => Self::v2_from_cbor_values(session, array, device_info),
            Value::Integer(i) => Self::v3_from_authenticated_request(session, array, i.into()),
            other => Err(anyhow!(
                "Expected integer or array at index {VERSION_OR_DEVICE_INFO_INDEX}, \
                found {other:?}"
            )),
        }
    }

    fn v2_from_cbor_values(
        session: &Session,
        mut csr: Vec<Value>,
        mut device_info: Vec<Value>,
    ) -> Result<Self> {
        let maced_keys_to_sign =
            FieldValue::from_optional_value("MacedKeysToSign", csr.pop()).into_cose_mac0()?;
        let encrypted_protected_data =
            FieldValue::from_optional_value("ProtectedData", csr.pop()).into_cose_encrypt()?;
        let challenge = FieldValue::from_optional_value("Challenge", csr.pop()).into_bytes()?;

        ensure!(device_info.len() == 2, "Device info should contain exactly 2 entries");
        device_info.pop(); // ignore unverified info
        let device_info = device_info.pop().unwrap();
        let device_info_serialized = serialize(device_info.clone());
        let device_info_canonicalized = canonicalize_map(device_info.clone())?;
        if device_info_canonicalized != device_info_serialized {
            match session.options.verbose {
                true => bail!(
                    "Device info is not canonical:\nexpected: {:?}\nactual: {:?}",
                    &hex::encode(device_info_canonicalized),
                    &hex::encode(device_info_serialized)
                ),
                false => bail!("Device info is not canonical"),
            }
        }
        let verified_device_info = match device_info {
            Value::Map(d) => Value::Map(d),
            other => bail!("Expected a map for verified device info, found '{:?}'", other),
        };

        let protected_data = ProtectedData::from_cose_encrypt(
            session,
            encrypted_protected_data,
            &challenge,
            &verified_device_info,
            &maced_keys_to_sign.tag,
        )?;

        let verified_device_info = match verified_device_info {
            Value::Map(m) => m,
            _ => unreachable!("verified device info is always a map"),
        };

        Ok(Self::V2 {
            device_info: DeviceInfo::from_cbor_values(
                verified_device_info,
                None, // version must be determined by "version" in DeviceInfo
                session.options.is_factory,
            )?,
            challenge,
            protected_data,
        })
    }

    fn v3_from_authenticated_request(
        session: &Session,
        mut csr: Vec<Value>,
        version: i128,
    ) -> Result<Self> {
        if version != 1 {
            bail!(
                "Invalid AuthenticatedRequest version. Only '1' is supported, found '{}",
                version
            );
        }

        // CSRs that are uploaded to the backend have an additional unverified info field tacked
        // onto them. We just ignore that, so if it's there pop it and move on.
        if csr.len() == 5 {
            FieldValue::from_optional_value("UnverifiedDeviceInfo", csr.pop());
        }
        if csr.len() != 4 {
            bail!("AuthenticatedRequest should have 4 elements. Found {}.", csr.len());
        }

        let signed_data =
            FieldValue::from_optional_value("SignedData", csr.pop()).into_cose_sign1()?;
        let raw_dice_chain = csr.pop().ok_or(anyhow!("Missing DiceCertChain"))?;
        let uds_certs = FieldValue::from_optional_value("UdsCerts", csr.pop()).into_map()?;

        let dice_chain = ChainForm::from_value(session, raw_dice_chain)?;
        let uds_certs = Self::parse_and_validate_uds_certs(&dice_chain, uds_certs)?;

        let signing_key = dice_chain.leaf_public_key();
        signing_key.verify_cose_sign1(&signed_data, &[]).context("verifying SignedData failed")?;

        let signed_data_payload = signed_data.payload.context("missing payload in SignedData")?;

        let mut signed_data_value = value_from_bytes(signed_data_payload.as_slice())
            .context("SignedData is not valid CBOR")?;

        let signed_data_array =
            signed_data_value.as_array_mut().context("SignedData is not a CBOR array")?;

        let csr_payload_value =
            signed_data_array.pop().context("Missing CsrPayload in SignedData")?;

        let csr_payload = CsrPayload::from_value(&csr_payload_value, session)
            .context("Unable to parse CsrPayload")?;

        let challenge = match signed_data_array.pop().context("missing challenge")?.into_bytes() {
            Ok(challenge) => challenge,
            Err(_) => bail!("Challenge is not bytes"),
        };

        Ok(Self::V3 { dice_chain, uds_certs, challenge, csr_payload })
    }

    fn parse_and_validate_uds_certs(
        dice_chain: &ChainForm,
        uds_certs: Vec<(Value, Value)>,
    ) -> Result<HashMap<String, Vec<X509>>> {
        let expected_uds = match dice_chain {
            ChainForm::Degenerate(chain) => chain.public_key(),
            ChainForm::Proper(chain) => chain.root_public_key(),
        }
        .pkey();

        let mut parsed = HashMap::new();
        for (signer, der_certs) in uds_certs {
            let signer = FieldValue::from_value("SignerName", signer).into_string()?;
            let x509_certs = FieldValue::from_value("UdsCertChain", der_certs)
                .into_array()?
                .into_iter()
                .map(|v| match FieldValue::from_value("X509Certificate", v).into_bytes() {
                    Ok(b) => X509::from_der(&b).context("Unable to parse DER X509Certificate"),
                    Err(e) => Err(e).context("Invalid type for X509Certificate"),
                })
                .collect::<Result<Vec<X509>>>()?;
            Self::validate_uds_cert_path(&signer, &x509_certs)?;
            ensure!(
                x509_certs.last().unwrap().public_key()?.public_eq(expected_uds),
                "UdsCert leaf for SignerName '{signer}' does not match the DICE chain root"
            );
            ensure!(
                parsed.insert(signer.clone(), x509_certs).is_none(),
                "Duplicate signer found: '{signer}'"
            );
        }
        Ok(parsed)
    }

    fn validate_uds_cert_path(signer: &String, certs: &Vec<X509>) -> Result<()> {
        ensure!(
            certs.len() > 1,
            "Certificate chain for signer '{signer}' is too short: {certs:#?}"
        );

        for cert in certs {
            let id = cert.public_key()?.id();
            ensure!(
                matches!(id, Id::RSA | Id::EC | Id::ED25519),
                "Certificate has an unsupported public algorithm id {id:?}"
            );
        }

        // OpenSSL wants us to split up root trust anchor, leaf, and intermediates
        let mut certs_copy = certs.clone();
        let leaf = certs_copy.pop().unwrap();
        let mut intermediates = Stack::new()?;
        while certs_copy.len() > 1 {
            intermediates.push(certs_copy.pop().unwrap())?;
        }
        let root = certs_copy.pop().unwrap();

        let mut root_store_builder = X509StoreBuilder::new()?;
        root_store_builder.add_cert(root)?;
        // Setting this flag causes the signature on the root certificate to be checked.
        // This ensures that the root certificate has not been corrupted.
        root_store_builder.set_flags(X509VerifyFlags::CHECK_SS_SIGNATURE)?;

        let root_store = root_store_builder.build();

        let mut store = X509StoreContext::new()?;
        let result = store.init(&root_store, &leaf, &intermediates, |context| {
            // the with_context function must return Result<T, ErrorStack>, so we have to get
            // tricky and return Result<Result<()>, ErrorStack> so we can bubble up custom errors.
            match context.verify_cert() {
                Ok(true) => (),
                Ok(false) => return Ok(Err(anyhow!("Cert failed to verify: {}", context.error()))),
                Err(e) => return Err(e),
            };

            if let Some(chain) = context.chain() {
                // OpenSSL returns the leaf at the bottom of the stack.
                if !chain.iter().rev().eq(certs.iter()) {
                    let chain: Vec<_> = chain.iter().rev().map(|r| r.to_owned()).collect();
                    return Ok(Err(anyhow!(
                        "Verified chain doesn't match input: {chain:#?} vs {certs:#?}"
                    )));
                }
            } else {
                return Ok(Err(anyhow!("Cert chain is missing (impossible!)")));
            }
            Ok(Ok(()))
        });

        match result {
            Ok(e) => e,
            Err(e) => bail!("Error verifying cert chain: {e:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    // More complete testing happens in the factorycsr module, as the test data
    // generation spits out full JSON files, not just a CSR. Therefore, only a
    // minimal number of smoke tests are here.
    use super::*;
    use crate::cbor::rkp::csr::testutil::{parse_pem_public_key_or_panic, test_device_info};
    use crate::dice::{ChainForm, DegenerateChain, DiceMode};
    use crate::rkp::{DeviceInfoSecurityLevel, DeviceInfoVersion};
    use crate::session::{Options, Session};
    use std::fs;

    #[test]
    fn from_base64_valid_v2() {
        let input = fs::read_to_string("testdata/csr/v2_csr.base64").unwrap().trim().to_owned();
        let csr = Csr::from_base64_cbor(&Session::default(), &input).unwrap();

        let device_info = testutil::test_device_info(DeviceInfoVersion::V2);
        let challenge =
            b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10".to_vec();
        let pem = "-----BEGIN PUBLIC KEY-----\n\
                   MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAERd9pHZbUJ/b4IleUGDN8fs8+LDxE\n\
                   vG6VX1dkw0sClFs4imbzfXGbocEq74S7TQiyZkd1LhY6HRZnTC51KoGDIA==\n\
                   -----END PUBLIC KEY-----\n";
        let subject_public_key = testutil::parse_pem_public_key_or_panic(pem);
        let degenerate = ChainForm::Degenerate(
            DegenerateChain::new("self-signed", "self-signed", subject_public_key).unwrap(),
        );
        let protected_data = ProtectedData::new(vec![0; 32], degenerate, None);
        assert_eq!(csr, Csr::V2 { device_info, challenge, protected_data });
    }

    #[test]
    fn from_base64_valid_v3() {
        let input = fs::read_to_string("testdata/csr/v3_csr.base64").unwrap().trim().to_owned();
        let csr = Csr::from_base64_cbor(&Session::default(), &input).unwrap();
        if let Csr::V3 { dice_chain, uds_certs, csr_payload, .. } = csr {
            assert_eq!(csr_payload.device_info, test_device_info(DeviceInfoVersion::V3));
            let root_public_key = parse_pem_public_key_or_panic(
                "-----BEGIN PUBLIC KEY-----\n\
                    MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEh5NUV4872vKEL3XPSp8lfkV4AN3J\n\
                KJti1Y5kbbR9ucTpSyoOjX9UmBCM/uuPU/MGXMWrgbBf3++02ALzC+V3eQ==\n\
                    -----END PUBLIC KEY-----\n",
            );
            match dice_chain {
                ChainForm::Proper(proper_chain) => {
                    assert_eq!(proper_chain.root_public_key(), &root_public_key);
                    let payloads = proper_chain.payloads();
                    assert_eq!(payloads.len(), 1);
                    assert_eq!(payloads[0].issuer(), "issuer");
                    assert_eq!(payloads[0].subject(), "subject");
                    assert_eq!(payloads[0].mode(), DiceMode::Normal);
                    assert_eq!(payloads[0].code_hash(), &[0x55; 32]);
                    let expected_config_hash: &[u8] =
                        b"\xb8\x96\x54\xe2\x2c\xa4\xd2\x4a\x9c\x0e\x45\x11\xc8\xf2\x63\xf0\
                          \x66\x0d\x2e\x20\x48\x96\x90\x14\xf4\x54\x63\xc4\xf4\x39\x30\x38";
                    assert_eq!(payloads[0].config_hash(), Some(expected_config_hash));
                    assert_eq!(payloads[0].authority_hash(), &[0x55; 32]);
                    assert_eq!(payloads[0].config_desc().component_name(), Some("component_name"));
                    assert_eq!(payloads[0].config_desc().component_version(), None);
                    assert!(!payloads[0].config_desc().resettable());
                    assert_eq!(payloads[0].config_desc().security_version(), None);
                    assert_eq!(payloads[0].config_desc().extensions(), []);
                }
                ChainForm::Degenerate(d) => panic!("Parsed chain is not proper: {:?}", d),
            }
            assert_eq!(uds_certs.len(), 0);
        } else {
            panic!("Parsed CSR was not V3: {:?}", csr);
        }
    }

    #[test]
    fn from_cbor_valid_v3_with_degenerate_chain() -> anyhow::Result<()> {
        let cbor = fs::read("testdata/csr/v3_csr_degenerate_chain.cbor")?;
        let session = Session { options: Options::vsr16() };
        Csr::from_cbor(&session, cbor.as_slice())?;
        Ok(())
    }

    #[test]
    fn from_cbor_valid_v3_avf_with_rkpvm_chain() -> anyhow::Result<()> {
        let input = fs::read("testdata/csr/v3_csr_avf.cbor")?;
        let mut session = Session::default();
        session.set_allow_any_mode(true);
        session.set_rkp_instance(RkpInstance::Avf);
        let csr = Csr::from_cbor(&session, input.as_slice())?;
        let Csr::V3 { dice_chain, csr_payload, .. } = csr else {
            panic!("Parsed CSR was not V3: {:?}", csr);
        };
        assert_eq!(csr_payload.device_info.security_level, DeviceInfoSecurityLevel::Avf);
        let ChainForm::Proper(proper_chain) = dice_chain else {
            panic!("Parsed chain is not proper: {:?}", dice_chain);
        };
        let expected_len = 7;
        assert_eq!(proper_chain.payloads().len(), expected_len);
        assert!(proper_chain.payloads()[expected_len - 1].has_rkpvm_marker());
        assert!(proper_chain.payloads()[expected_len - 2].has_rkpvm_marker());
        Ok(())
    }

    #[test]
    fn from_empty_string() {
        let err = Csr::from_base64_cbor(&Session::default(), &"").unwrap_err();
        assert!(err.to_string().contains("invalid CBOR"));
    }

    #[test]
    fn from_garbage() {
        let err = Csr::from_base64_cbor(&Session::default(), &"cnViYmlzaAo=").unwrap_err();
        assert!(err.to_string().contains("invalid CBOR"));
    }

    #[test]
    fn from_invalid_base64() {
        let err = Csr::from_base64_cbor(&Session::default(), &"not base64").unwrap_err();
        assert!(err.to_string().contains("invalid base64"));
    }

    const VALID_UDS_CHAIN: &[&str] = &[
        "-----BEGIN CERTIFICATE-----\n\
    MIICKjCCAbCgAwIBAgIUPFTOIhGtj7sELYJk5HicdV8r/x8wCgYIKoZIzj0EAwMw\n\
    RzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUxGjAY\n\
    BgNVBAMMEVRFU1QgSU5URVJNRURJQVRFMCAXDTI0MTExNDIwMTcwOFoYDzIxMjQx\n\
    MDIxMjAxNzA4WjA/MQswCQYDVQQGEwJVUzELMAkGA1UECAwCQ0ExDzANBgNVBAoM\n\
    Bkdvb2dsZTESMBAGA1UEAwwJVEVTVCBMRUFGMHYwEAYHKoZIzj0CAQYFK4EEACID\n\
    YgAEry9HebgpyEnmimjtgs1KN5akdUx6cAEKVwkj0ZkYIW9V+YeRa4ap4yWvh8ZG\n\
    U1GA0Eu26z7YQZbPuJ8LnyW0cXj3UGpXgP8EWyftWdz9EX6WpzdO7fuxtxeC/X2l\n\
    ZuFIo2MwYTAdBgNVHQ4EFgQUWl8nH6cOAU3IrNZ2kqOzq3JUlukwHwYDVR0jBBgw\n\
    FoAUjtSEVIqjzE6pGwlgEHPRn5o9a0YwDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8B\n\
    Af8EBAMCB4AwCgYIKoZIzj0EAwMDaAAwZQIxAMmpFFiMRVnZHZSBCqjWQfA0lqaT\n\
    HiusLqIEcAobDy80/mzO2yO6exNjoXkMB17COwIwD1YmiMkaqnnJkan9CNTnBXZB\n\
    WNlU9CCE10ohcVfjssl7YVcnna70Rc1UH4DhjSj6\n\
    -----END CERTIFICATE-----",
        "-----BEGIN CERTIFICATE-----\n\
    MIICLjCCAbOgAwIBAgIUKIsXCCFZRvz0BYboKmgZjyGArAEwCgYIKoZIzj0EAwMw\n\
    PzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUxEjAQ\n\
    BgNVBAMMCVRFU1QgUk9PVDAgFw0yNDExMTQyMDE1MzVaGA8yMTI0MTAyMTIwMTUz\n\
    NVowRzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUx\n\
    GjAYBgNVBAMMEVRFU1QgSU5URVJNRURJQVRFMHYwEAYHKoZIzj0CAQYFK4EEACID\n\
    YgAEFYWPvG5PCQBBXFi/xY1F3MRqDXHkmqdTErc3wlBakVQmCjiklrEalZhMAr5Q\n\
    0MYje5/l/ZbN+bvurD5ZsOyWRSrzTkzoUMQszB4fSoJtBp3grcEfd+/tQlC1DZO0\n\
    wTROo2YwZDAdBgNVHQ4EFgQUjtSEVIqjzE6pGwlgEHPRn5o9a0YwHwYDVR0jBBgw\n\
    FoAUwQ91rFNLmFq9YMlG1bqk7OvWk44wEgYDVR0TAQH/BAgwBgEB/wIBADAOBgNV\n\
    HQ8BAf8EBAMCAgQwCgYIKoZIzj0EAwMDaQAwZgIxAMWXmsh6d8YSkP1+wR9eMDCe\n\
    9G0EFAPOn+BiKfthnnboRUEr8BuIt3w9SkEDCdWfcAIxAMJ99xkGf3bcdykao4jh\n\
    bgG844IvDSx11EwzQV/kcteHOut93YO0D83CgkDc2C4dNA==\n\
    -----END CERTIFICATE-----",
        "-----BEGIN CERTIFICATE-----\n\
    MIICJTCCAaugAwIBAgIUUo4NdEcdRuQdrm5Trm5x+qvx2LEwCgYIKoZIzj0EAwMw\n\
    PzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUxEjAQ\n\
    BgNVBAMMCVRFU1QgUk9PVDAgFw0yNDExMTQyMDEzNDRaGA8yMTI0MTAyMTIwMTM0\n\
    NFowPzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUx\n\
    EjAQBgNVBAMMCVRFU1QgUk9PVDB2MBAGByqGSM49AgEGBSuBBAAiA2IABOGIoNBS\n\
    sVs+mTjZpqOyoWTEOIvIIhuFfi49eqleyKTnekgXyXcJfqppsbqYcgPKaTbJmhU/\n\
    iuOjaSIUlyf5tjJ7bIOAngopcH6u+Qky/a2Q///eOIl7U9WhEMnSYwZ7rqNmMGQw\n\
    HQYDVR0OBBYEFMEPdaxTS5havWDJRtW6pOzr1pOOMB8GA1UdIwQYMBaAFMEPdaxT\n\
    S5havWDJRtW6pOzr1pOOMA4GA1UdDwEB/wQEAwICBDASBgNVHRMBAf8ECDAGAQH/\n\
    AgEBMAoGCCqGSM49BAMDA2gAMGUCMDa2TefBEmKLebf6KziawLXeQRhqb4wcMgtE\n\
    RUZ7JOojBC6CqN7xqPMIo2Pp9Pn6iwIxANlSkus723tk6OdeG33A++HwZ9KIXzU4\n\
    cJUsEeE4pQ5exYACy2Nd+LVtmerw8ZF6xg==\n\
    -----END CERTIFICATE-----",
    ];

    const INVALID_UDS_ROOT: &str = "-----BEGIN CERTIFICATE-----\n\
    MIICJTCCAaugAwIBAgIUUo4NdEcdRuQdrm5Trm5x+qvx2LEwCgYIKoZIzj0EAwMw\n\
    PzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUxEjAQ\n\
    BgNVBAMMCVRFU1QgUk9PVDAgFw0yNDExMTQyMDEzNDRaGA8yMTI0MTAyMTIwMTM0\n\
    NFowPzELMAkGA1UEBhMCVVMxCzAJBgNVBAgMAkNBMQ8wDQYDVQQKDAZHb29nbGUx\n\
    EjAQBgNVBAMMCVRFU1QgUk9PVDB2MBAGByqGSM49AgEGBSuBBAAiA2IABOGIoNBS\n\
    sVs+mTjZpqOyoWTEOIvIIhuFfi49eqleyKTnekgXyXcJfqppsbqYcgPKaTbJmhU/\n\
    iuOjaSIUlyf5tjJ7bIOAngopcH6u+Qky/a2Q///eOIl7U9WhEMnSYwZ7rqNmMGQw\n\
    HQYDVR0OBBYEFMEPdaxTS5havWDJRtW6pOzr1pOOMB8GA1UdIwQYMBaAFMEPdaxT\n\
    S5havWDJRtW6pOzr1pOOMA4GA1UdDwEB/wQEAwICBDASBgNVHRMBAf8ECDAGAQH/\n\
    AgEBMAoGCCqGSM49BAMDA2gAMGUCMDa2TefBEmKLebf6KziawLXeQRhqb4wcMgtE\n\
    RUZ7JOojBC6CqN7xqPMIo2Pp9Pn6iwIxANlSkus723tk6OdeG33A++HwZ9KIXzU4\n\
    cJUsEeE4pQ5exYACy2Ndthisisaproblem==\n\
    -----END CERTIFICATE-----";

    #[test]
    fn verify_a_valid_cert_chain() {
        let leaf = X509::from_pem(VALID_UDS_CHAIN[0].as_bytes()).unwrap();
        let intermediate = X509::from_pem(VALID_UDS_CHAIN[1].as_bytes()).unwrap();
        let root = X509::from_pem(VALID_UDS_CHAIN[2].as_bytes()).unwrap();
        let certs = vec![root, intermediate, leaf];
        let signer = "Test Signer".to_string();
        let result = Csr::validate_uds_cert_path(&signer, &certs);
        assert!(result.is_ok());
    }

    #[test]
    fn make_sure_root_signature_is_checked() {
        let leaf = X509::from_pem(VALID_UDS_CHAIN[0].as_bytes()).unwrap();
        let intermediate = X509::from_pem(VALID_UDS_CHAIN[1].as_bytes()).unwrap();
        let valid_root = X509::from_pem(VALID_UDS_CHAIN[2].as_bytes()).unwrap();
        let invalid_root = X509::from_pem(INVALID_UDS_ROOT.as_bytes()).unwrap();

        let valid_root_public_key = valid_root.public_key().unwrap();
        let invalid_root_public_key = invalid_root.public_key().unwrap();
        assert!(invalid_root_public_key.public_eq(&valid_root_public_key));

        let certs = vec![invalid_root.clone(), intermediate.clone(), leaf.clone()];
        let signer = "Test Signer".to_string();
        let error = Csr::validate_uds_cert_path(&signer, &certs).unwrap_err();
        assert!(error.to_string().contains("certificate signature failure"));

        let mut intermediates = Stack::new().unwrap();
        intermediates.push(intermediate).unwrap();

        let mut builder = X509StoreBuilder::new().unwrap();
        builder.add_cert(invalid_root).unwrap();
        let store = builder.build();

        let mut context = X509StoreContext::new().unwrap();
        assert!(context.init(&store, &leaf, &intermediates, |c| c.verify_cert()).unwrap());
    }
}

#[cfg(test)]
pub(crate) mod testutil {
    use crate::publickey::PublicKey;
    use crate::rkp::{
        DeviceInfo, DeviceInfoBootloaderState, DeviceInfoSecurityLevel, DeviceInfoVbState,
        DeviceInfoVersion,
    };
    use openssl::pkey::PKey;

    // Parse the given PEM-encoded public key into a PublicKey object, panicking on failure.
    pub fn parse_pem_public_key_or_panic(pem: &str) -> PublicKey {
        PKey::public_key_from_pem(pem.as_bytes()).unwrap().try_into().unwrap()
    }

    // The test data uses mostly common DeviceInfo fields
    pub fn test_device_info(version: DeviceInfoVersion) -> DeviceInfo {
        DeviceInfo {
            version,
            brand: "Google".to_string(),
            manufacturer: "Google".to_string(),
            product: "pixel".to_string(),
            model: "model".to_string(),
            device: "device".to_string(),
            vb_state: DeviceInfoVbState::Green,
            bootloader_state: DeviceInfoBootloaderState::Locked,
            vbmeta_digest: b"\x11\x22\x33\x44\x55\x66\x77\x88\x99\xaa\xbb\xcc\xdd\xee\xff".to_vec(),
            os_version: Some("12".to_string()),
            system_patch_level: 20221025,
            boot_patch_level: 20221026,
            vendor_patch_level: 20221027,
            security_level: DeviceInfoSecurityLevel::Tee,
            fused: 1,
        }
    }
}
