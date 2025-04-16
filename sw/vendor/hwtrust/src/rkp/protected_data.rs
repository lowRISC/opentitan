use anyhow::Result;
use openssl::x509::X509;
use std::{collections::HashMap, fmt};

use crate::dice::ChainForm;

/// The CSR V2 payload that is encrypted with an Endpoint Encryption Key (EEK).
#[derive(Clone, Eq, PartialEq)]
pub struct ProtectedData {
    mac_key: Vec<u8>,
    dice_chain: ChainForm,
    uds_certs: Option<UdsCerts>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct UdsCerts(pub(crate) HashMap<String, UdsCertsEntry>);

/// Represent entries in the UDS certs mapping as an enum to support special cases in the future
/// where the input is not actually x.509 certs.
#[derive(Clone, Eq, PartialEq)]
pub enum UdsCertsEntry {
    /// A chain of X.509 certificates that certify the UDS
    X509Chain(Vec<Vec<u8>>),
}

impl ProtectedData {
    /// Constructs a new `ProtectedData` with a MAC key, DICE chain, and optional UDS certificates.
    pub fn new(mac_key: Vec<u8>, dice_chain: ChainForm, uds_certs: Option<UdsCerts>) -> Self {
        Self { mac_key, dice_chain, uds_certs }
    }

    /// Returns the DICE chain.
    pub fn dice_chain(&self) -> ChainForm {
        self.dice_chain.clone()
    }

    /// Returns the UDS certificates.
    pub fn uds_certs(&self) -> Option<UdsCerts> {
        self.uds_certs.clone()
    }
}

impl UdsCerts {
    pub fn new() -> Self {
        Self(HashMap::new())
    }
}

impl UdsCertsEntry {
    pub(crate) fn new_x509_chain(der_encoded_chain: Vec<Vec<u8>>) -> Result<Self> {
        Ok(Self::X509Chain(der_encoded_chain))
    }
}

impl fmt::Debug for ProtectedData {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        fmt.debug_struct("ProtectedData")
            .field("mac_key", &hex::encode(&self.mac_key))
            .field("dice_chain", &self.dice_chain)
            .field("uds_certs", &self.uds_certs)
            .finish()
    }
}

impl fmt::Debug for UdsCertsEntry {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::X509Chain(v) => format_x509_chain(fmt, v),
        }
    }
}

fn format_x509_chain(fmt: &mut fmt::Formatter, chain: &Vec<Vec<u8>>) -> fmt::Result {
    for c in chain {
        fmt.write_str(&x509_der_to_pem(c).unwrap_or("[INVALID CERTIFICATE]".to_string()))?;
    }
    Ok(())
}

fn x509_der_to_pem(der: &[u8]) -> Result<String> {
    let utf8 = X509::from_der(der)?.to_pem()?;
    Ok(std::str::from_utf8(&utf8)?.to_string())
}
