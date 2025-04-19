use crate::dice::Payload;
use crate::publickey::PublicKey;
use crate::session::RkpInstance;
use anyhow::Result;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use thiserror::Error;

/// The minimum number of RKP VM markers required in a valid [RKP VM DICE chain][rkpvm-chain].
///
/// An RKP VM chain must have a continuous presence of RKP VM markers, starting from a DICE
/// certificate derived in the TEE and extending to the leaf DICE certificate.
/// Therefore, a valid RKP VM chain should have at least two DICE certificates with RKP VM markers:
///
/// * One added in the pVM (managed by Android).
/// * One added in the TEE (managed by vendors).
///
/// [rkpvm-chain]: https://android.googlesource.com/platform/packages/modules/Virtualization/+/main/docs/vm_remote_attestation.md
const RKPVM_CHAIN_MIN_MARKER_NUM: usize = 2;

/// Enumeration of the different forms that a DICE chain can take.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ChainForm {
    /// A proper DICE chain with multiple layers of trust.
    Proper(Chain),
    /// A degenerate DICE chain consisting of a single self-signed certificate.
    Degenerate(DegenerateChain),
}

/// Represents a DICE chain. This consists of the root public key (which signs the first
/// certificate), followed by a chain of certificates.
#[derive(Clone, Eq, PartialEq)]
pub struct Chain {
    root_public_key: PublicKey,
    payloads: Vec<Payload>,
}

#[derive(Error, Debug, PartialEq, Eq)]
pub(crate) enum ValidationError {
    #[error("no payloads")]
    NoPayloads,
    #[error("issuer `{1}` is not previous subject `{2}` in payload {0}")]
    IssuerMismatch(usize, String, String),
    #[error("repeated subject in payload {0}")]
    RepeatedSubject(usize, String),
    #[error("repeated key in payload {0}")]
    RepeatedKey(usize),
    #[error("RKP VM chain has discontinuous marker at the {0}th payload")]
    RkpVmChainHasDiscontinuousMarker(usize),
    #[error(
        "RKP VM chain does not have enough RKP VM markers. \
         Minimal marker number:{RKPVM_CHAIN_MIN_MARKER_NUM}, actual marker number:{0}"
    )]
    NotEnoughRkpVmMarker(usize),
    #[error("non RKP VM chain should not have continuous RKP VM markers")]
    UnexpectedRkpVmMarkers,
}

impl ChainForm {
    pub(crate) fn leaf_public_key(&self) -> &PublicKey {
        match self {
            Self::Proper(chain) => chain.leaf().subject_public_key(),
            Self::Degenerate(degenerate) => degenerate.public_key(),
        }
    }

    /// Return the length of the chain.
    pub fn length(&self) -> usize {
        match self {
            ChainForm::Proper(chain) => chain.payloads.len(),
            ChainForm::Degenerate(_) => 1,
        }
    }
}

impl Chain {
    /// Builds a [`Chain`] after checking that it is well-formed. The issuer of each entry must be
    /// equal to the subject of the previous entry. The chain is not allowed to contain any
    /// repeated subjects or subject public keys as that would suggest something untoward has
    /// happened.
    ///
    /// Additionally, `rkp_instance` provides additional context for the validation of the chain
    /// according to the instance-specific chain validation rules.
    ///
    /// * AVF instance: The chain is validated against the RKP VM chain validation rules.
    /// * Non-AVF instances: The chain must not contain RKP VM markers that conform to the RKP VM
    ///   chain validation rules.
    pub(crate) fn validate(
        root_public_key: PublicKey,
        payloads: Vec<Payload>,
        rkp_instance: RkpInstance,
    ) -> Result<Self, ValidationError> {
        if payloads.is_empty() {
            return Err(ValidationError::NoPayloads);
        }

        let mut subjects = HashSet::with_capacity(payloads.len());
        let mut keys = HashSet::with_capacity(1 + payloads.len());
        keys.insert(root_public_key.to_pem());

        let mut previous_subject: Option<&str> = None;
        for (n, payload) in payloads.iter().enumerate() {
            if let Some(previous_subject) = previous_subject {
                if payload.issuer() != previous_subject {
                    return Err(ValidationError::IssuerMismatch(
                        n,
                        payload.issuer().to_string(),
                        previous_subject.to_string(),
                    ));
                }
            }
            if subjects.replace(payload.subject()).is_some() {
                return Err(ValidationError::RepeatedSubject(n, payload.subject().to_string()));
            }
            if keys.replace(payload.subject_public_key().to_pem()).is_some() {
                return Err(ValidationError::RepeatedKey(n));
            }
            previous_subject = Some(payload.subject());
        }
        match rkp_instance {
            RkpInstance::Avf => validate_rkpvm_chain(&payloads),
            _ => validate_non_rkpvm_chain(&payloads),
        }?;
        Ok(Self { root_public_key, payloads })
    }

    /// Get the root public key which verifies the first certificate in the chain.
    pub fn root_public_key(&self) -> &PublicKey {
        &self.root_public_key
    }

    /// Get the payloads of the certificates in the chain, from root to leaf.
    pub fn payloads(&self) -> &[Payload] {
        &self.payloads
    }

    /// Get the payload from the final certificate in the chain.
    pub fn leaf(&self) -> &Payload {
        // There is always at least one payload.
        self.payloads.last().unwrap()
    }
}

fn validate_rkpvm_chain(payloads: &[Payload]) -> Result<(), ValidationError> {
    let mut rkpvm_marker_count = 0;
    for (i, payload) in payloads.iter().enumerate() {
        if payload.has_rkpvm_marker() {
            rkpvm_marker_count += 1;
        } else if rkpvm_marker_count > 0 {
            return Err(ValidationError::RkpVmChainHasDiscontinuousMarker(i));
        }
    }
    if rkpvm_marker_count < RKPVM_CHAIN_MIN_MARKER_NUM {
        return Err(ValidationError::NotEnoughRkpVmMarker(rkpvm_marker_count));
    }
    Ok(())
}

/// Validates a DICE chain that is not associated with an RKP VM.
///
/// While non-RKP VM DICE chains might contain RKP VM markers in some vendor DICE certificates
/// (e.g., Microdroid pVM DICE chain), they should not have a continuous presence of markers up to
/// the last certificate in the chain.
fn validate_non_rkpvm_chain(payloads: &[Payload]) -> Result<(), ValidationError> {
    validate_rkpvm_chain(payloads).map_or(Ok(()), |_| Err(ValidationError::UnexpectedRkpVmMarkers))
}

impl Display for Chain {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        writeln!(f, "Root public key:")?;
        writeln!(f, "{}", self.root_public_key.to_pem())?;
        for (i, payload) in self.payloads.iter().enumerate() {
            writeln!(f, "Cert {}:", i)?;
            writeln!(f, "{}", payload)?;
        }
        Ok(())
    }
}

impl fmt::Debug for Chain {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        let mut debug = fmt.debug_struct("Chain");
        debug.field("Root public key", &self.root_public_key.to_pem());
        for (i, payload) in self.payloads.iter().enumerate() {
            debug.field(&format!("DICE Certificate[{i}]"), payload);
        }
        debug.finish()
    }
}

#[derive(Error, Debug, PartialEq, Eq)]
pub(crate) enum DegenerateChainError {
    #[error("issuer empty")]
    IssuerEmpty,
    #[error("subject empty")]
    SubjectEmpty,
}

/// A degenerate DICE chain. These chains consist of a single, self-signed certificate and the
/// entries contain less information than usual. They are expected from devices that haven't
/// implemented everything necessary to produce a proper DICE Chain.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DegenerateChain {
    issuer: String,
    subject: String,
    subject_public_key: PublicKey,
}

impl DegenerateChain {
    pub(crate) fn new<I: Into<String>, S: Into<String>>(
        issuer: I,
        subject: S,
        subject_public_key: PublicKey,
    ) -> Result<Self, DegenerateChainError> {
        let issuer = issuer.into();
        let subject = subject.into();
        if issuer.is_empty() {
            return Err(DegenerateChainError::IssuerEmpty);
        }
        if subject.is_empty() {
            return Err(DegenerateChainError::SubjectEmpty);
        }
        Ok(Self { issuer, subject, subject_public_key })
    }

    /// Gets the issuer of the degenerate chain.
    pub fn issuer(&self) -> &str {
        &self.issuer
    }

    /// Gets the subject of the degenerate chain.
    pub fn subject(&self) -> &str {
        &self.subject
    }

    /// Gets the public key of the degenerate chain.
    pub fn public_key(&self) -> &PublicKey {
        &self.subject_public_key
    }
}

impl Display for DegenerateChain {
    fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
        writeln!(f, "Public key:")?;
        writeln!(f, "{}", self.public_key().to_pem())?;
        writeln!(f, "Issuer: {}", self.issuer)?;
        writeln!(f, "Subject: {}", self.subject)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dice::{ConfigDescBuilder, DiceMode, PayloadBuilder};
    use crate::publickey::testkeys::{PrivateKey, ED25519_KEY_PEM, P256_KEY_PEM, P384_KEY_PEM};

    #[test]
    fn chain_validate_valid() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let keys = P256_KEY_PEM[1..4].iter().copied().enumerate();
        let payloads = keys.map(|(n, key)| valid_payload(n, key).build().unwrap()).collect();
        Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap();
    }

    #[test]
    fn chain_validate_valid_with_mixed_kinds_of_key() {
        let root_public_key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        let keys = [P256_KEY_PEM[0], P384_KEY_PEM[0]].into_iter().enumerate();
        let payloads = keys.map(|(n, key)| valid_payload(n, key).build().unwrap()).collect();
        Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap();
    }

    #[test]
    fn chain_validate_fails_without_payloads() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let payloads = Vec::new();
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap_err();
        assert_eq!(err, ValidationError::NoPayloads);
    }

    #[test]
    fn chain_validate_fails_when_root_key_repeated() {
        let key = P256_KEY_PEM[0];
        let root_public_key = PrivateKey::from_pem(key).public_key();
        let payloads = vec![valid_payload(0, key).build().unwrap()];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap_err();
        assert_eq!(err, ValidationError::RepeatedKey(0));
    }

    #[test]
    fn chain_validate_fails_with_repeated_subject_public_keys() {
        let repeated_key = P256_KEY_PEM[0];
        let root_public_key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        let payloads = vec![
            valid_payload(0, repeated_key).build().unwrap(),
            valid_payload(1, repeated_key).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap_err();
        assert_eq!(err, ValidationError::RepeatedKey(1));
    }

    #[test]
    fn chain_validate_fails_with_repeated_subjects() {
        let keys = &P256_KEY_PEM[..3];
        let repeated = "match";
        let root_public_key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        let payloads = vec![
            valid_payload(0, keys[0]).subject(repeated).build().unwrap(),
            valid_payload(1, keys[1]).issuer(repeated).build().unwrap(),
            valid_payload(2, keys[2]).subject(repeated).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap_err();
        assert_eq!(err, ValidationError::RepeatedSubject(2, repeated.into()));
    }

    #[test]
    fn chain_validate_fails_with_mismatching_issuer_and_subject() {
        let expected = "expected";
        let wrong = "wrong";
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).subject(expected).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).issuer(wrong).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap_err();
        assert_eq!(err, ValidationError::IssuerMismatch(1, wrong.into(), expected.into()));
    }

    #[test]
    fn non_rkpvm_chain_validate_with_discontinuous_markers() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let config_desc = ConfigDescBuilder::new().rkp_vm_marker(true).build();
        // This chain resembles a Microdroid pVM DICE chain where vendors add RKP VM markers in
        // the vendor part of the chain, while pVM does not.
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).config_desc(config_desc.clone()).build().unwrap(),
            valid_payload(2, P256_KEY_PEM[3]).build().unwrap(),
        ];
        Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap();
    }

    #[test]
    fn non_rkpvm_chain_validate_fails_with_continuous_markers() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let config_desc = ConfigDescBuilder::new().rkp_vm_marker(true).build();
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).config_desc(config_desc.clone()).build().unwrap(),
            valid_payload(2, P256_KEY_PEM[3]).config_desc(config_desc.clone()).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Default).unwrap_err();
        assert_eq!(err, ValidationError::UnexpectedRkpVmMarkers);
    }

    #[test]
    fn rkpvm_chain_validate_with_continuous_markers() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let config_desc = ConfigDescBuilder::new().rkp_vm_marker(true).build();
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).config_desc(config_desc.clone()).build().unwrap(),
            valid_payload(2, P256_KEY_PEM[3]).config_desc(config_desc.clone()).build().unwrap(),
        ];
        Chain::validate(root_public_key, payloads, RkpInstance::Avf).unwrap();
    }

    #[test]
    fn rkpvm_chain_validate_fails_with_no_marker() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let payloads = vec![valid_payload(0, P256_KEY_PEM[1]).build().unwrap()];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Avf).unwrap_err();
        assert_eq!(err, ValidationError::NotEnoughRkpVmMarker(0));
    }

    #[test]
    fn rkpvm_chain_validate_fails_with_not_enough_markers() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let config_desc = ConfigDescBuilder::new().rkp_vm_marker(true).build();
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).config_desc(config_desc).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Avf).unwrap_err();
        assert_eq!(err, ValidationError::NotEnoughRkpVmMarker(1));
    }

    #[test]
    fn rkpvm_chain_validate_fails_with_discontinous_markers() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let config_desc = ConfigDescBuilder::new().rkp_vm_marker(true).build();
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).config_desc(config_desc.clone()).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).build().unwrap(),
            valid_payload(2, P256_KEY_PEM[3]).config_desc(config_desc.clone()).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Avf).unwrap_err();
        assert_eq!(err, ValidationError::RkpVmChainHasDiscontinuousMarker(1));
    }

    #[test]
    fn rkpvm_chain_validate_fails_last_payload_has_no_marker() {
        let root_public_key = PrivateKey::from_pem(P256_KEY_PEM[0]).public_key();
        let config_desc = ConfigDescBuilder::new().rkp_vm_marker(true).build();
        let payloads = vec![
            valid_payload(0, P256_KEY_PEM[1]).config_desc(config_desc.clone()).build().unwrap(),
            valid_payload(1, P256_KEY_PEM[2]).config_desc(config_desc.clone()).build().unwrap(),
            valid_payload(2, P256_KEY_PEM[3]).build().unwrap(),
        ];
        let err = Chain::validate(root_public_key, payloads, RkpInstance::Avf).unwrap_err();
        assert_eq!(err, ValidationError::RkpVmChainHasDiscontinuousMarker(2));
    }

    fn valid_payload(index: usize, pem: &str) -> PayloadBuilder {
        PayloadBuilder::with_subject_public_key(PrivateKey::from_pem(pem).public_key())
            .issuer(format!("component {}", index))
            .subject(format!("component {}", index + 1))
            .mode(DiceMode::Normal)
            .code_hash(vec![0; 64])
            .authority_hash(vec![0; 64])
    }

    #[test]
    fn degenerate_chain_valid() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        DegenerateChain::new("issuer", "issuer", key).unwrap();
    }

    #[test]
    fn degenerate_chain_empty_issuer() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        let err = DegenerateChain::new("", "subject", key).unwrap_err();
        assert_eq!(err, DegenerateChainError::IssuerEmpty);
    }

    #[test]
    fn degenerate_chain_empty_subject() {
        let key = PrivateKey::from_pem(ED25519_KEY_PEM[0]).public_key();
        let err = DegenerateChain::new("issuer", "", key).unwrap_err();
        assert_eq!(err, DegenerateChainError::SubjectEmpty);
    }
}
