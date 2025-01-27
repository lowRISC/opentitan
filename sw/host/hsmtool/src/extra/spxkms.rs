// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use acorn::{GenerateFlags, KeyEntry, KeyInfo, SpxInterface};
use anyhow::{anyhow, Context, Result};
use base64ct::{Base64, Encoding};
use indexmap::IndexMap;
use serde::{de::DeserializeOwned, Deserialize, Serialize};
use serde_json::Value;
use sphincsplus::{SphincsPlus, SpxDomain, SpxPublicKey};
use std::process::Command;
use std::str::FromStr;
use thiserror::Error;
use zeroize::Zeroizing;

use reqwest::blocking::Client;
use reqwest::{IntoUrl, Url};

use crate::error::HsmError;

/// SpxEf implements SPHINCS+ signing via Google CloudKms.
pub struct SpxKms {
    keyring: Url,
    project: String,
    auth: Zeroizing<String>,
}

/// ApiError represents an error result from the cloud API.
#[derive(Deserialize, Debug, Error)]
#[error("api error: code={code} message={message:?}; details={details:?}")]
#[serde(rename_all = "camelCase")]
pub struct ApiError {
    pub code: u32,
    pub message: String,
    pub status: String,
    #[serde(flatten)]
    pub details: IndexMap<String, Value>,
}

// CloudResult assists in deserializing the cloud API return into an error
// or a specific type.
#[derive(Deserialize, Debug)]
enum CloudResult<T> {
    #[serde(rename = "error")]
    Error(ApiError),
    #[serde(untagged)]
    Ok(T),
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsKeyList {
    crypto_keys: Vec<KmsKeyRef>,
}

// Note: dead_code is allowed because some of the fields defined in this struct
// are not used, but are fields returned by the KMS json API.
#[allow(dead_code)]
#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct VersionTemplate {
    #[serde(default)]
    protection_level: String,
    #[serde(default)]
    algorithm: String,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsCreateKey {
    purpose: String,
    version_template: VersionTemplate,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsKeyRef {
    name: String,
    version_template: VersionTemplate,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsKeyVersion {
    name: String,
    state: String,
    #[serde(default)]
    algorithm: String,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsKeyVersions {
    crypto_key_versions: Vec<KmsKeyVersion>,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsPublicKeyData {
    data: String,
}

// Note: dead_code is allowed because some of the fields defined in this struct
// are not used, but are fields returned by the KMS json API.
#[allow(dead_code)]
#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
struct KmsPublicKey {
    algorithm: String,
    name: String,
    #[serde(default)]
    protection_level: String,
    #[serde(default)]
    public_key_format: String,
    pem: Option<String>,
    public_key: Option<KmsPublicKeyData>,
}

#[derive(Serialize, Debug)]
struct KmsDigest {
    sha256: String,
}

#[derive(Serialize, Debug)]
struct KmsSignRequest {
    #[serde(skip_serializing_if = "Option::is_none")]
    digest: Option<KmsDigest>,
    #[serde(skip_serializing_if = "Option::is_none")]
    data: Option<String>,
}

impl SpxKms {
    const ALGORITHM: &'static str = "PQ_SIGN_SLH_DSA_SHA2_128S";

    pub fn new(parameters: &str) -> Result<Box<Self>> {
        let output = Command::new("gcloud")
            .args(["auth", "print-access-token"])
            .output()?;
        if output.status.success() {
            // Get the authorization token and strip trailing newlines.
            let mut auth = String::from_utf8(output.stdout)?;
            let len = auth.trim_end().len();
            auth.truncate(len);

            let mut params = IndexMap::new();
            params.extend(parameters.split(':').map(|p| {
                p.split_once('=')
                    .expect("KMS parameters should be key=value")
            }));

            let project = params.get("project").ok_or(HsmError::Unsupported(
                "KMS requires a project parameter".into(),
            ))?;
            let location = params.get("location").ok_or(HsmError::Unsupported(
                "KMS requires a location parameter".into(),
            ))?;
            let keyring = params.get("keyring").ok_or(HsmError::Unsupported(
                "KMS requires a keyring parameter".into(),
            ))?;
            let url = format!("https://cloudkms.googleapis.com/v1/projects/{project}/locations/{location}/keyRings/{keyring}/");
            log::info!("keyring url: {url}");
            Ok(Box::new(Self {
                keyring: Url::parse(&url)?,
                project: project.to_string(),
                auth: auth.into(),
            }))
        } else {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(anyhow!("gcloud error {:?}: {}", output.status, stderr))
        }
    }

    fn get<RSP: DeserializeOwned>(&self, url: impl IntoUrl) -> Result<RSP> {
        let client = Client::new();
        log::debug!("GET {}", url.as_str());
        let resp = client
            .get(url)
            .bearer_auth(&*self.auth)
            .header("content-type", "application/json")
            .header("X-Goog-User-Project", &self.project)
            .send()?;
        let data = resp.text()?;
        log::debug!("data: {data}");
        match serde_json::from_str::<CloudResult<RSP>>(&data)? {
            CloudResult::Error(e) => Err(e.into()),
            CloudResult::Ok(v) => Ok(v),
        }
    }

    fn post<RSP: DeserializeOwned>(&self, url: impl IntoUrl, req: &impl Serialize) -> Result<RSP> {
        let client = Client::new();
        log::debug!("POST {}", url.as_str());
        let resp = client
            .post(url)
            .bearer_auth(&*self.auth)
            .header("content-type", "application/json")
            .header("X-Goog-User-Project", &self.project)
            .json(req)
            .send()?;
        let data = resp.text()?;
        log::debug!("data: {data}");
        match serde_json::from_str::<CloudResult<RSP>>(&data)? {
            CloudResult::Error(e) => Err(e.into()),
            CloudResult::Ok(v) => Ok(v),
        }
    }

    fn get_key_version(&self, alias: &str) -> Result<KmsKeyVersion> {
        let url = self
            .keyring
            .join(&format!("cryptoKeys/{alias}/cryptoKeyVersions"))?;
        let versions = self.get::<KmsKeyVersions>(url)?;
        match versions
            .crypto_key_versions
            .iter()
            .filter(|v| v.state == "ENABLED" && v.algorithm == Self::ALGORITHM)
            .last()
        {
            Some(key) => Ok(key.clone()),
            None => Err(HsmError::ObjectNotFound(alias.into()).into()),
        }
    }

    fn get_public_key(&self, alias: &str) -> Result<KmsPublicKey> {
        let key = self.get_key_version(alias)?;
        let url = self.keyring.join(&format!("/v1/{}/publicKey", key.name))?;
        self.get(url)
    }
}

impl SpxInterface for SpxKms {
    /// Get the version of the backend.
    fn get_version(&self) -> Result<String> {
        Ok(String::from("CloudKMS 0.0.1"))
    }

    /// List keys known to the backend.
    fn list_keys(&self) -> Result<Vec<KeyEntry>> {
        let keys = self.keyring.join("cryptoKeys")?;
        let keys = self.get::<KmsKeyList>(keys)?;
        let mut result = Vec::new();

        for k in keys.crypto_keys.iter() {
            let (_, name) = k
                .name
                .rsplit_once('/')
                .ok_or_else(|| HsmError::ParseError("could not parse key name".into()))
                .with_context(|| format!("key name {:?}", k.name))?;
            if k.version_template.algorithm != Self::ALGORITHM {
                continue;
            }
            let key = self.get_key_version(name)?;
            result.push(KeyEntry {
                alias: name.into(),
                hash: None,
                algorithm: key.algorithm.clone(),
                ..Default::default()
            });
        }
        Ok(result)
    }

    /// Get the public key info.
    fn get_key_info(&self, alias: &str) -> Result<KeyInfo> {
        let key = self.get_public_key(alias)?;
        let algorithm = key
            .algorithm
            .trim_start_matches("PQ_SIGN_")
            .replace('_', "-");
        let data = if let Some(pem) = &key.pem {
            pem.as_str()
        } else if let Some(public_key) = &key.public_key {
            public_key.data.as_str()
        } else {
            return Err(HsmError::Unsupported("did not find public key material".into()).into());
        };
        Ok(KeyInfo {
            hash: "".into(),
            algorithm,
            public_key: Base64::decode_vec(data)?,
            private_blob: Vec::new(),
        })
    }

    /// Generate a key pair.
    fn generate_key(
        &self,
        alias: &str,
        _algorithm: &str,
        _token: &str,
        flags: GenerateFlags,
    ) -> Result<KeyEntry> {
        if flags.contains(GenerateFlags::EXPORT_PRIVATE) {
            return Err(HsmError::Unsupported("export of private key material".into()).into());
        }
        let url = self
            .keyring
            .join(&format!("cryptoKeys?crypto_key_id={alias}"))?;
        let template = KmsCreateKey {
            purpose: "ASYMMETRIC_SIGN".into(),
            version_template: VersionTemplate {
                algorithm: Self::ALGORITHM.into(),
                protection_level: "SOFTWARE".into(),
            },
        };
        let resp = self.post::<KmsKeyRef>(url, &template)?;
        Ok(KeyEntry {
            alias: alias.into(),
            algorithm: resp
                .version_template
                .algorithm
                .trim_start_matches("PQ_SIGN_")
                .replace('_', "-"),
            ..Default::default()
        })
    }

    /// Import a key pair.
    fn import_keypair(
        &self,
        _alias: &str,
        _algorithm: &str,
        _token: &str,
        _overwrite: bool,
        _public_key: &[u8],
        _private_key: &[u8],
    ) -> Result<KeyEntry> {
        Err(HsmError::Unsupported(format!(
            "key import is not supported by {}",
            self.get_version()?
        ))
        .into())
    }

    /// Sign a message.
    fn sign(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
    ) -> Result<Vec<u8>> {
        match domain {
            SpxDomain::Pure => {}
            _ => {
                return Err(HsmError::Unsupported(format!(
                    "domain {domain} not supported by {}",
                    self.get_version()?
                ))
                .into())
            }
        };
        let alias = alias.ok_or(HsmError::NoSearchCriteria)?;
        if key_hash.is_some() {
            log::warn!("ignored key_hash {key_hash:?}");
        }
        let key = self.get_key_version(alias)?;
        let url = self
            .keyring
            .join(&format!("/v1/{}:asymmetricSign", key.name))?;
        let req = KmsSignRequest {
            digest: None,
            data: Some(Base64::encode_string(message)),
        };
        let resp = self.post::<IndexMap<String, String>>(url, &req)?;
        let signature = Base64::decode_vec(&resp["signature"])?;
        Ok(signature)
    }

    /// Verify a message.
    fn verify(
        &self,
        alias: Option<&str>,
        key_hash: Option<&str>,
        domain: SpxDomain,
        message: &[u8],
        signature: &[u8],
    ) -> Result<bool> {
        let alias = alias.ok_or(HsmError::NoSearchCriteria)?;
        if key_hash.is_some() {
            log::warn!("ignored key_hash {key_hash:?}");
        }
        let info = self.get_key_info(alias)?;
        let pk =
            SpxPublicKey::from_bytes(SphincsPlus::from_str(&info.algorithm)?, &info.public_key)?;
        match pk.verify(domain, signature, message) {
            Ok(_) => Ok(true),
            Err(_) => Ok(false),
        }
    }
}
