use crate::publickey::PublicKey;
use std::fmt::{self, Display, Formatter};
use thiserror::Error;

/// Enumeration of modes used in the DICE chain payloads.
#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub enum DiceMode {
    /// This mode also acts as a catch-all for configurations which do not fit the other modes and
    /// invalid modes.
    #[default]
    NotConfigured,
    /// The device is operating normally under secure configuration.
    Normal,
    /// At least one criterion for [`Normal`] is not met and the device is not in a secure state.
    Debug,
    /// A recovery or maintenance mode of some kind.
    Recovery,
}

/// The payload of a DICE chain entry.
#[derive(Clone, Eq, PartialEq)]
pub struct Payload {
    issuer: String,
    subject: String,
    subject_public_key: PublicKey,
    mode: DiceMode,
    code_desc: Option<Vec<u8>>,
    code_hash: Vec<u8>,
    config_desc: ConfigDesc,
    config_hash: Option<Vec<u8>>,
    authority_desc: Option<Vec<u8>>,
    authority_hash: Vec<u8>,
}

impl Payload {
    /// Gets the issuer of the payload.
    pub fn issuer(&self) -> &str {
        &self.issuer
    }

    /// Gets the subject of the payload.
    pub fn subject(&self) -> &str {
        &self.subject
    }

    /// Gets the subject public key of the payload.
    pub fn subject_public_key(&self) -> &PublicKey {
        &self.subject_public_key
    }

    /// Gets the mode of the payload.
    pub fn mode(&self) -> DiceMode {
        self.mode
    }

    /// Gets the code descriptor of the payload.
    pub fn code_desc(&self) -> Option<&[u8]> {
        self.code_desc.as_deref()
    }

    /// Gets the code hash of the payload.
    pub fn code_hash(&self) -> &[u8] {
        &self.code_hash
    }

    /// Gets the configuration descriptor of the payload.
    pub fn config_desc(&self) -> &ConfigDesc {
        &self.config_desc
    }

    /// Gets the configuration hash of the payload.
    pub fn config_hash(&self) -> Option<&[u8]> {
        self.config_hash.as_deref()
    }

    /// Gets the authority descriptor of the payload.
    pub fn authority_desc(&self) -> Option<&[u8]> {
        self.authority_desc.as_deref()
    }

    /// Gets the authority hash of the payload.
    pub fn authority_hash(&self) -> &[u8] {
        &self.authority_hash
    }

    /// Returns whether the payload has an RKP VM marker.
    pub fn has_rkpvm_marker(&self) -> bool {
        self.config_desc.rkp_vm_marker()
    }
}

impl Display for Payload {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        writeln!(f, "Issuer: {}", self.issuer)?;
        writeln!(f, "Subject: {}", self.subject)?;
        writeln!(f, "Mode: {:?}", self.mode)?;
        if let Some(code_desc) = &self.code_desc {
            writeln!(f, "Code Desc: {}", hex::encode(code_desc))?;
        }
        writeln!(f, "Code Hash: {}", hex::encode(&self.code_hash))?;
        if let Some(config_hash) = &self.config_hash {
            writeln!(f, "Config Hash: {}", hex::encode(config_hash))?;
        }
        if let Some(authority_desc) = &self.authority_desc {
            writeln!(f, "Authority Desc: {}", hex::encode(authority_desc))?;
        }
        writeln!(f, "Authority Hash: {}", hex::encode(&self.authority_hash))?;
        writeln!(f, "Config Desc {{")?;
        write!(f, "{}", &self.config_desc)?;
        writeln!(f, "}}")?;
        Ok(())
    }
}

impl fmt::Debug for Payload {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        let mut debug = f.debug_struct("Payload");
        debug.field("Issuer", &self.issuer);
        debug.field("Subject", &self.subject);
        debug.field("Mode", &self.mode);
        if let Some(code_desc) = &self.code_desc {
            debug.field("Code Desc", &hex::encode(code_desc));
        }
        debug.field("Code Hash", &hex::encode(&self.code_hash));
        if let Some(config_hash) = &self.config_hash {
            debug.field("Config Hash", &hex::encode(config_hash));
        }
        if let Some(authority_desc) = &self.authority_desc {
            debug.field("Authority Desc", &hex::encode(authority_desc));
        }
        debug.field("Authority Hash", &hex::encode(&self.authority_hash));
        debug.field("Config Desc", &self.config_desc);
        debug.finish()
    }
}

#[derive(Error, Debug, PartialEq, Eq)]
pub(crate) enum PayloadBuilderError {
    #[error("issuer empty")]
    IssuerEmpty,
    #[error("subject empty")]
    SubjectEmpty,
}

pub(crate) struct PayloadBuilder(Payload);

impl PayloadBuilder {
    /// Constructs a new builder with the given subject public key.
    pub fn with_subject_public_key(subject_public_key: PublicKey) -> Self {
        Self(Payload {
            issuer: Default::default(),
            subject: Default::default(),
            subject_public_key,
            mode: Default::default(),
            code_desc: Default::default(),
            code_hash: Default::default(),
            config_desc: Default::default(),
            config_hash: Default::default(),
            authority_desc: Default::default(),
            authority_hash: Default::default(),
        })
    }

    /// Builds the [`Payload`] after validating the issuer and subject.
    pub fn build(self) -> Result<Payload, PayloadBuilderError> {
        if self.0.issuer.is_empty() {
            return Err(PayloadBuilderError::IssuerEmpty);
        }
        if self.0.subject.is_empty() {
            return Err(PayloadBuilderError::SubjectEmpty);
        }
        Ok(self.0)
    }

    /// Sets the issuer of the payload.
    #[must_use]
    pub fn issuer<S: Into<String>>(mut self, issuer: S) -> Self {
        self.0.issuer = issuer.into();
        self
    }

    /// Sets the subject of the payload.
    #[must_use]
    pub fn subject<S: Into<String>>(mut self, subject: S) -> Self {
        self.0.subject = subject.into();
        self
    }

    /// Sets the mode of the payload.
    #[must_use]
    pub fn mode(mut self, mode: DiceMode) -> Self {
        self.0.mode = mode;
        self
    }

    /// Sets the code descriptor of the payload.
    #[must_use]
    pub fn code_desc(mut self, code_desc: Option<Vec<u8>>) -> Self {
        self.0.code_desc = code_desc;
        self
    }

    /// Sets the code hash of the payload.
    #[must_use]
    pub fn code_hash(mut self, code_hash: Vec<u8>) -> Self {
        self.0.code_hash = code_hash;
        self
    }

    /// Sets the configuration descriptor of the payload.
    #[must_use]
    pub fn config_desc(mut self, config_desc: ConfigDesc) -> Self {
        self.0.config_desc = config_desc;
        self
    }

    /// Sets the configuration hash of the payload.
    #[must_use]
    pub fn config_hash(mut self, config_hash: Option<Vec<u8>>) -> Self {
        self.0.config_hash = config_hash;
        self
    }

    /// Sets the authority descriptor of the payload.
    #[must_use]
    pub fn authority_desc(mut self, authority_desc: Option<Vec<u8>>) -> Self {
        self.0.authority_desc = authority_desc;
        self
    }

    /// Sets the authority hash of the payload.
    #[must_use]
    pub fn authority_hash(mut self, authority_hash: Vec<u8>) -> Self {
        self.0.authority_hash = authority_hash;
        self
    }
}

/// Version of the component from the configuration descriptor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ComponentVersion {
    /// An integer component version number.
    Integer(i64),
    /// A free-form string component version.
    String(String),
}

impl Display for ComponentVersion {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        match self {
            ComponentVersion::Integer(n) => write!(f, "{n}")?,
            ComponentVersion::String(s) => write!(f, "{s}")?,
        }
        Ok(())
    }
}

/// Fields from the configuration descriptor.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ConfigDesc {
    component_name: Option<String>,
    component_instance_name: Option<String>,
    component_version: Option<ComponentVersion>,
    resettable: bool,
    security_version: Option<u64>,
    rkp_vm_marker: bool,
    extensions: Vec<(i64, Vec<u8>)>,
}

impl ConfigDesc {
    /// Gets the component name.
    pub fn component_name(&self) -> Option<&str> {
        self.component_name.as_deref()
    }

    /// Gets the component instance name.
    pub fn component_instance_name(&self) -> Option<&str> {
        self.component_instance_name.as_deref()
    }

    /// Gets the component version.
    pub fn component_version(&self) -> Option<&ComponentVersion> {
        self.component_version.as_ref()
    }

    /// Returns whether the component is factory resettable.
    pub fn resettable(&self) -> bool {
        self.resettable
    }

    /// Gets the security version.
    pub fn security_version(&self) -> Option<u64> {
        self.security_version
    }

    /// Returns whether the component may be part of an RPK VM.
    pub fn rkp_vm_marker(&self) -> bool {
        self.rkp_vm_marker
    }

    /// Return any extensions present in the descriptor.
    pub fn extensions(&self) -> &[(i64, Vec<u8>)] {
        &self.extensions
    }
}

impl Display for ConfigDesc {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        if let Some(component_name) = &self.component_name {
            writeln!(f, "Component Name: {}", component_name)?;
        }
        if let Some(component_instance_name) = &self.component_instance_name {
            writeln!(f, "Component Instance Name: {}", component_instance_name)?;
        }
        if let Some(component_version) = &self.component_version {
            writeln!(f, "Component Version: {}", component_version)?;
        }
        if self.resettable {
            writeln!(f, "Resettable")?;
        }
        if let Some(security_version) = &self.security_version {
            writeln!(f, "Security Version: {}", security_version)?;
        }
        if self.rkp_vm_marker {
            writeln!(f, "RKP VM Marker")?;
        }
        for (key, value) in &self.extensions {
            writeln!(f, "{key}: {value:?}")?;
        }
        Ok(())
    }
}

pub(crate) struct ConfigDescBuilder(ConfigDesc);

impl ConfigDescBuilder {
    /// Constructs a new builder with default values.
    pub fn new() -> Self {
        Self(ConfigDesc::default())
    }

    /// Builds the [`ConfigDesc`].
    pub fn build(self) -> ConfigDesc {
        self.0
    }

    /// Sets the component name.
    #[must_use]
    pub fn component_name(mut self, name: Option<String>) -> Self {
        self.0.component_name = name;
        self
    }

    /// Sets the component instance name.
    #[must_use]
    pub fn component_instance_name(mut self, name: Option<String>) -> Self {
        self.0.component_instance_name = name;
        self
    }

    /// Sets the component version.
    #[must_use]
    pub fn component_version(mut self, version: Option<ComponentVersion>) -> Self {
        self.0.component_version = version;
        self
    }

    /// Sets whether the component is factory resettable.
    #[must_use]
    pub fn resettable(mut self, resettable: bool) -> Self {
        self.0.resettable = resettable;
        self
    }

    /// Sets the security version.
    #[must_use]
    pub fn security_version(mut self, version: Option<u64>) -> Self {
        self.0.security_version = version;
        self
    }

    /// Sets whether the component may be part of an RKP VM.
    #[must_use]
    pub fn rkp_vm_marker(mut self, rkp_vm_marker: bool) -> Self {
        self.0.rkp_vm_marker = rkp_vm_marker;
        self
    }

    /// Sets the extension key/value pairs.
    #[must_use]
    pub fn extensions(mut self, extensions: Vec<(i64, Vec<u8>)>) -> Self {
        self.0.extensions = extensions;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::publickey::testkeys::{PrivateKey, P256_KEY_PEM};

    #[test]
    fn payload_builder_valid() {
        valid_payload().build().unwrap();
    }

    #[test]
    fn payload_builder_valid_512_bit_hashes() {
        valid_payload()
            .code_hash(vec![1; 64])
            .authority_hash(vec![2; 64])
            .config_hash(Some(vec![3; 64]))
            .build()
            .unwrap();
    }

    #[test]
    fn payload_builder_valid_384_bit_hashes() {
        valid_payload()
            .code_hash(vec![1; 48])
            .authority_hash(vec![2; 48])
            .config_hash(Some(vec![3; 48]))
            .build()
            .unwrap();
    }

    #[test]
    fn payload_builder_valid_256_bit_hashes() {
        valid_payload()
            .code_hash(vec![1; 32])
            .authority_hash(vec![2; 32])
            .config_hash(Some(vec![3; 32]))
            .build()
            .unwrap();
    }

    #[test]
    fn payload_builder_empty_issuer() {
        let err = valid_payload().issuer("").build().unwrap_err();
        assert_eq!(err, PayloadBuilderError::IssuerEmpty);
    }

    #[test]
    fn payload_builder_empty_subject() {
        let err = valid_payload().subject("").build().unwrap_err();
        assert_eq!(err, PayloadBuilderError::SubjectEmpty);
    }

    fn valid_payload() -> PayloadBuilder {
        let key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        PayloadBuilder::with_subject_public_key(key)
            .issuer("issuer")
            .subject("subject")
            .code_hash(vec![1; 64])
            .authority_hash(vec![2; 64])
    }
}
