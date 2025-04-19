use crate::rkp::Csr;
use crate::session::{RkpInstance, Session};
use anyhow::{bail, Result};
use serde_json::{Map, Value};
use std::str::FromStr;

/// Represents a "Factory CSR", which is a JSON value captured for each device on the factory
/// line. This JSON is uploaded to the RKP backend to register the device. We reuse the CSR
/// (Certificate Signing Request) format for this as an implementation convenience. The CSR
/// actually contains an empty set of keys for which certificates are needed.
#[non_exhaustive]
#[derive(Debug, PartialEq)]
pub struct FactoryCsr {
    /// The CSR, as created by an IRemotelyProvisionedComponent HAL.
    pub csr: Csr,
    /// The name of the HAL that generated the CSR.
    pub name: String,
}

fn get_string_from_map(fields: &Map<String, Value>, key: &str) -> Result<String> {
    match fields.get(key) {
        Some(Value::String(s)) => Ok(s.to_string()),
        Some(v) => bail!("Unexpected type for '{key}'. Expected String, found '{v:?}'"),
        None => bail!("Unable to locate '{key}' in input"),
    }
}

impl FactoryCsr {
    /// Parse the input JSON string into a CSR that was captured on the factory line. The
    /// format of the JSON data is defined by rkp_factory_extraction_tool.
    pub fn from_json(session: &Session, json: &str) -> Result<Self> {
        match serde_json::from_str(json) {
            Ok(Value::Object(map)) => Self::from_map(session, map),
            Ok(unexpected) => bail!("Expected a map, got some other type: {unexpected}"),
            Err(e) => bail!("Error parsing input json: {e}"),
        }
    }

    fn from_map(session: &Session, fields: Map<String, Value>) -> Result<Self> {
        let base64 = get_string_from_map(&fields, "csr")?;
        let name = get_string_from_map(&fields, "name")?;
        let mut new_session = session.clone();
        new_session.set_rkp_instance(RkpInstance::from_str(&name)?);
        let csr = Csr::from_base64_cbor(&new_session, &base64)?;
        Ok(Self { csr, name })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cbor::rkp::csr::testutil::{parse_pem_public_key_or_panic, test_device_info};
    use crate::dice::{ChainForm, DegenerateChain};
    use crate::rkp::device_info::DeviceInfoVersion;
    use crate::rkp::factory_csr::FactoryCsr;
    use crate::rkp::{ProtectedData, UdsCerts, UdsCertsEntry};
    use anyhow::anyhow;
    use itertools::Itertools;
    use openssl::{pkey::PKey, x509::X509};
    use std::fs;
    use std::fs::File;

    fn json_map_from_file(path: &str) -> Result<Map<String, Value>> {
        let input = File::open(path)?;
        match serde_json::from_reader(input)? {
            Value::Object(map) => Ok(map),
            other => Err(anyhow!("Unexpected JSON. Wanted a map, found {other:?}")),
        }
    }

    #[test]
    fn from_json_valid_v2_ed25519() {
        let json = fs::read_to_string("testdata/factory_csr/v2_ed25519_valid.json").unwrap();
        let csr = FactoryCsr::from_json(&Session::default(), &json).unwrap();
        let subject_public_key = parse_pem_public_key_or_panic(
            "-----BEGIN PUBLIC KEY-----\n\
            MCowBQYDK2VwAyEAOhWsfxcBLgUfLLdqpb8cLUWutkkPtfIqDRfJC3LUihI=\n\
            -----END PUBLIC KEY-----\n",
        );
        let degenerate = ChainForm::Degenerate(
            DegenerateChain::new("self-signed", "self-signed", subject_public_key).unwrap(),
        );
        let chain = [
            "-----BEGIN CERTIFICATE-----\n\
             MIIBaDCCARqgAwIBAgIBezAFBgMrZXAwKzEVMBMGA1UEChMMRmFrZSBDb21wYW55\n\
             MRIwEAYDVQQDEwlGYWtlIFJvb3QwHhcNMjMwODAxMjI1MTM0WhcNMjMwODMxMjI1\n\
             MTM0WjArMRUwEwYDVQQKEwxGYWtlIENvbXBhbnkxEjAQBgNVBAMTCUZha2UgUm9v\n\
             dDAqMAUGAytlcAMhAJYhPNIeQXe6+GPFiQAg4WtK+D8HuWaF6Es4X3HgDzq7o2Mw\n\
             YTAdBgNVHQ4EFgQUDR0DF3abDeR3WXSlIhpN07R049owHwYDVR0jBBgwFoAUDR0D\n\
             F3abDeR3WXSlIhpN07R049owDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8EBAMC\n\
             AgQwBQYDK2VwA0EAWNEhXrATWj4MXT/n38OwbngUm/n/5+vGFqV0aXuJPX/8d6Yx\n\
             BbX/LFv6m8/VuPuItSqK4AudgwZJoupR/lknDg==\n\
             -----END CERTIFICATE-----\n",
            "-----BEGIN CERTIFICATE-----\n\
             MIIBbDCCAR6gAwIBAgICAcgwBQYDK2VwMCsxFTATBgNVBAoTDEZha2UgQ29tcGFu\n\
             eTESMBAGA1UEAxMJRmFrZSBSb290MB4XDTIzMDgwMTIyNTEzNFoXDTIzMDgzMTIy\n\
             NTEzNFowLjEVMBMGA1UEChMMRmFrZSBDb21wYW55MRUwEwYDVQQDEwxGYWtlIENo\n\
             aXBzZXQwKjAFBgMrZXADIQA6Fax/FwEuBR8st2qlvxwtRa62SQ+18ioNF8kLctSK\n\
             EqNjMGEwHQYDVR0OBBYEFEbOrkgBL2SUCLJayyvpc+oR7m6/MB8GA1UdIwQYMBaA\n\
             FA0dAxd2mw3kd1l0pSIaTdO0dOPaMA8GA1UdEwEB/wQFMAMBAf8wDgYDVR0PAQH/\n\
             BAQDAgIEMAUGAytlcANBANJmKGgiZP3tqtjnHpbmR3ypkXtvuqmo6KTBIHKsGKAO\n\
             mH8qlMQPLmNSdxTs3OnVrlxQwZqXxHjVHS/6OpkkFgo=\n\
             -----END CERTIFICATE-----\n",
        ];
        let chain = chain
            .iter()
            .map(|pem| X509::from_pem(pem.as_bytes()).unwrap().to_der().unwrap())
            .collect_vec();

        let mut uds_certs = UdsCerts::new();
        uds_certs
            .0
            .insert("google-test".to_string(), UdsCertsEntry::new_x509_chain(chain).unwrap());
        assert_eq!(
            csr,
            FactoryCsr {
                csr: Csr::V2 {
                    device_info: test_device_info(DeviceInfoVersion::V2),
                    challenge: b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10"
                        .to_vec(),
                    protected_data: ProtectedData::new(vec![0; 32], degenerate, Some(uds_certs)),
                },
                name: "default".to_string(),
            }
        );
    }

    #[test]
    fn from_json_valid_v3_ed25519() {
        let json = fs::read_to_string("testdata/factory_csr/v3_ed25519_valid.json").unwrap();
        let csr = FactoryCsr::from_json(&Session::default(), &json).unwrap();
        if let Csr::V3 { dice_chain, uds_certs, csr_payload, .. } = csr.csr {
            assert_eq!(csr_payload.device_info, test_device_info(DeviceInfoVersion::V3));
            let root_public_key = parse_pem_public_key_or_panic(
                "-----BEGIN PUBLIC KEY-----\n\
                    MCowBQYDK2VwAyEArqr7jIIQ8TB1+l/Sh69eiSJL6t6txO1oLhpkdVSUuBk=\n\
                    -----END PUBLIC KEY-----\n",
            );
            match dice_chain {
                ChainForm::Proper(p) => {
                    assert_eq!(p.root_public_key(), &root_public_key);
                    assert_eq!(p.payloads().len(), 1);
                }
                ChainForm::Degenerate(d) => panic!("Parsed chain is not proper: {:?}", d),
            }
            assert_eq!(uds_certs.len(), 0);
        } else {
            panic!("Parsed CSR was not V3: {:?}", csr);
        }
    }

    #[test]
    fn from_json_valid_v2_p256() {
        let json = fs::read_to_string("testdata/factory_csr/v2_p256_valid.json").unwrap();
        let csr = FactoryCsr::from_json(&Session::default(), &json).unwrap();
        let pem = "-----BEGIN PUBLIC KEY-----\n\
                   MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAERd9pHZbUJ/b4IleUGDN8fs8+LDxE\n\
                   vG6VX1dkw0sClFs4imbzfXGbocEq74S7TQiyZkd1LhY6HRZnTC51KoGDIA==\n\
                   -----END PUBLIC KEY-----\n";
        let subject_public_key =
            PKey::public_key_from_pem(pem.as_bytes()).unwrap().try_into().unwrap();
        let degenerate = ChainForm::Degenerate(
            DegenerateChain::new("self-signed", "self-signed", subject_public_key).unwrap(),
        );
        assert_eq!(
            csr,
            FactoryCsr {
                csr: Csr::V2 {
                    device_info: test_device_info(DeviceInfoVersion::V2),
                    challenge: b"\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\x0d\x0e\x0f\x10"
                        .to_vec(),
                    protected_data: ProtectedData::new(vec![0; 32], degenerate, None),
                },
                name: "default".to_string(),
            }
        );
    }

    #[test]
    fn from_json_valid_v3_p256() {
        let json = fs::read_to_string("testdata/factory_csr/v3_p256_valid.json").unwrap();
        let csr = FactoryCsr::from_json(&Session::default(), &json).unwrap();
        if let Csr::V3 { dice_chain, uds_certs, csr_payload, .. } = csr.csr {
            assert_eq!(csr_payload.device_info, test_device_info(DeviceInfoVersion::V3));
            let root_public_key = parse_pem_public_key_or_panic(
                "-----BEGIN PUBLIC KEY-----\n\
                    MFkwEwYHKoZIzj0CAQYIKoZIzj0DAQcDQgAEh5NUV4872vKEL3XPSp8lfkV4AN3J\n\
                KJti1Y5kbbR9ucTpSyoOjX9UmBCM/uuPU/MGXMWrgbBf3++02ALzC+V3eQ==\n\
                    -----END PUBLIC KEY-----\n",
            );
            match dice_chain {
                ChainForm::Proper(p) => {
                    assert_eq!(p.root_public_key(), &root_public_key);
                    assert_eq!(p.payloads().len(), 1);
                }
                ChainForm::Degenerate(d) => panic!("Parsed chain is not proper: {:?}", d),
            }
            assert_eq!(uds_certs.len(), 0);
        } else {
            panic!("Parsed CSR was not V3: {:?}", csr);
        }
    }

    fn get_pem_or_die(cert: Option<&X509>) -> String {
        let cert = cert.unwrap_or_else(|| panic!("Missing x.509 cert"));
        let pem =
            cert.to_pem().unwrap_or_else(|e| panic!("Failed to encode X.509 cert to PEM: {e}"));
        String::from_utf8_lossy(&pem).to_string()
    }

    #[test]
    fn from_json_valid_v3_p256_with_uds_certs() {
        let json =
            fs::read_to_string("testdata/factory_csr/v3_p256_valid_with_uds_certs.json").unwrap();
        let csr = FactoryCsr::from_json(&Session::default(), &json).unwrap();
        if let Csr::V3 { uds_certs, .. } = csr.csr {
            assert_eq!(uds_certs.len(), 1);
            let chain = uds_certs.get("test-signer-name").unwrap_or_else(|| {
                panic!("Unable to find 'test-signer-name' in UdsCerts: {uds_certs:?}")
            });
            assert_eq!(chain.len(), 2);
            assert_eq!(
                get_pem_or_die(chain.first()),
                "-----BEGIN CERTIFICATE-----\n\
                MIIBaDCCARqgAwIBAgIBezAFBgMrZXAwKzEVMBMGA1UEChMMRmFrZSBDb21wYW55\n\
                MRIwEAYDVQQDEwlGYWtlIFJvb3QwHhcNMjQxMTA3MTMwOTMxWhcNNDkxMTAxMTMw\n\
                OTMxWjArMRUwEwYDVQQKEwxGYWtlIENvbXBhbnkxEjAQBgNVBAMTCUZha2UgUm9v\n\
                dDAqMAUGAytlcAMhAOgFrCrwxUYuOBSIk31/ykUsDP1vSRCzs8x2e8u8vumIo2Mw\n\
                YTAdBgNVHQ4EFgQUtLO8kYH4qiyhGNKhkzZvxk7td94wHwYDVR0jBBgwFoAUtLO8\n\
                kYH4qiyhGNKhkzZvxk7td94wDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8EBAMC\n\
                AgQwBQYDK2VwA0EA1o8kJ3NTsY7B5/rRkJi8i/RZE1/0pQC2OUTOi8S7ZCkVdBJK\n\
                7RyHo5/rVPXwVcsd3ZU1jZQalooek4mbDAWxAw==\n\
                -----END CERTIFICATE-----\n"
            );
            assert_eq!(
                get_pem_or_die(chain.get(1)),
                "-----BEGIN CERTIFICATE-----\n\
                MIIBmzCCAU2gAwIBAgICAcgwBQYDK2VwMCsxFTATBgNVBAoTDEZha2UgQ29tcGFu\n\
                eTESMBAGA1UEAxMJRmFrZSBSb290MB4XDTI0MTEwNzEzMDkzMVoXDTQ5MTEwMTEz\n\
                MDkzMVowLjEVMBMGA1UEChMMRmFrZSBDb21wYW55MRUwEwYDVQQDEwxGYWtlIENo\n\
                aXBzZXQwWTATBgcqhkjOPQIBBggqhkjOPQMBBwNCAATmCOHpHOZzSZvp1frFACgm\n\
                Itnj33YAKYseZfT68AlrN4UtC5boNVU5wjKWQFRcOlup5kxX2UVlb+jFCO7eskFU\n\
                o2MwYTAdBgNVHQ4EFgQU7KrNWsfWHijorD/+b5TBIZCzj3MwHwYDVR0jBBgwFoAU\n\
                tLO8kYH4qiyhGNKhkzZvxk7td94wDwYDVR0TAQH/BAUwAwEB/zAOBgNVHQ8BAf8E\n\
                BAMCAgQwBQYDK2VwA0EAuDdXCHTYt92UxftrDJnKXxjtDBCYMqXSlIuYw8p1W/UP\n\
                Ccerp/jUng8ELnfPj2ZTkTP2+NhvwsYKvbaxaz9pDA==\n\
                -----END CERTIFICATE-----\n"
            );
        } else {
            panic!("Parsed CSR was not V3: {:?}", csr);
        }
    }

    #[test]
    fn from_json_v3_p256_with_mismatch_uds_certs() {
        let json =
            fs::read_to_string("testdata/factory_csr/v3_p256_mismatched_uds_certs.json").unwrap();
        let err = FactoryCsr::from_json(&Session::default(), &json).unwrap_err();
        assert!(
            err.to_string().contains("does not match the DICE chain root"),
            "Expected mismatch between UDS_pub and UdsCerts leaf"
        );
    }

    #[test]
    fn from_json_v3_p256_with_extra_uds_cert_in_chain() {
        let json = fs::read_to_string("testdata/factory_csr/v3_p256_extra_uds_cert_in_chain.json")
            .unwrap();
        let err = FactoryCsr::from_json(&Session::default(), &json).unwrap_err();
        assert!(
            err.to_string().contains("Verified chain doesn't match input"),
            "Expected cert validation to fail due to extra cert in UDS chain"
        );
    }

    #[test]
    fn from_json_name_is_missing() {
        let mut value = json_map_from_file("testdata/factory_csr/v2_ed25519_valid.json").unwrap();
        value.remove_entry("name");
        let json = serde_json::to_string(&value).unwrap();
        let err = FactoryCsr::from_json(&Session::default(), &json).unwrap_err();
        assert!(err.to_string().contains("Unable to locate 'name'"));
    }

    #[test]
    fn from_json_name_is_wrong_type() {
        let mut value = json_map_from_file("testdata/factory_csr/v2_ed25519_valid.json").unwrap();
        value.insert("name".to_string(), Value::Object(Map::default()));
        let json = serde_json::to_string(&value).unwrap();
        let err = FactoryCsr::from_json(&Session::default(), &json).unwrap_err();
        assert!(err.to_string().contains("Unexpected type for 'name'"));
    }

    #[test]
    fn from_json_csr_is_missing() {
        let json = r#"{ "name": "default" }"#;
        let err = FactoryCsr::from_json(&Session::default(), json).unwrap_err();
        assert!(err.to_string().contains("Unable to locate 'csr'"));
    }

    #[test]
    fn from_json_csr_is_wrong_type() {
        let json = r#"{ "csr": 3.1415, "name": "default" }"#;
        let err = FactoryCsr::from_json(&Session::default(), json).unwrap_err();
        assert!(err.to_string().contains("Unexpected type for 'csr'"));
    }

    #[test]
    fn from_json_extra_tag_is_ignored() {
        let mut value = json_map_from_file("testdata/factory_csr/v2_ed25519_valid.json").unwrap();
        value.insert("extra".to_string(), Value::Bool(true));
        let json = serde_json::to_string(&value).unwrap();
        let csr = FactoryCsr::from_json(&Session::default(), &json).unwrap();
        assert_eq!(csr.name, "default");
    }

    #[test]
    fn from_json_valid_v3_avf_with_rkpvm_markers() {
        let json = fs::read_to_string("testdata/factory_csr/v3_avf_valid_with_rkpvm_markers.json")
            .unwrap();
        let mut session = Session::default();
        session.set_allow_any_mode(true);
        let csr = FactoryCsr::from_json(&session, &json).unwrap();
        assert_eq!(csr.name, "avf");
    }

    #[test]
    fn from_json_v3_p256_with_private_key() {
        let json =
            fs::read_to_string("testdata/factory_csr/v3_p256_with_private_key.json").unwrap();
        let err = FactoryCsr::from_json(&Session::default(), &json).unwrap_err();
        let source = err.source().unwrap().to_string();
        assert!(
            source.contains("disallowed labels should be empty")
                && source
                    .contains("12953f77f0726491a09c5b2d134a26a8a657dbc170c4036ffde81e881e0acd03")
        );
    }

    #[test]
    fn from_json_v3_p256_with_corrupted_payload() {
        let json =
            fs::read_to_string("testdata/factory_csr/v3_p256_with_corrupted_payload.json").unwrap();
        let err = FactoryCsr::from_json(&Session::default(), &json).unwrap_err();
        let source = err.source().unwrap().to_string();
        assert!(source.contains("Signature verification failed"));
    }
}
