// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::slh_dsa::SlhDsaError;
use crate::util::attribute::AttrData;
use asn1::{ObjectIdentifier, oid};

#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    num_enum::IntoPrimitive,
    clap::ValueEnum,
    serde::Serialize,
    serde::Deserialize,
)]
#[repr(u64)]
/// SLH-DSA Parameter Sets.
pub enum SlhDsaParameterSet {
    #[serde(rename = "CKP_SLH_DSA_SHA2_128S")]
    Sha2_128S = cryptoki_sys::CKP_SLH_DSA_SHA2_128S,
    #[serde(rename = "CKP_SLH_DSA_SHAKE_128S")]
    #[value(name = "shake-128s")]
    Shake128S = cryptoki_sys::CKP_SLH_DSA_SHAKE_128S,
    #[serde(rename = "CKP_SLH_DSA_SHA2_128F")]
    Sha2_128F = cryptoki_sys::CKP_SLH_DSA_SHA2_128F,
    #[serde(rename = "CKP_SLH_DSA_SHAKE_128F")]
    #[value(name = "shake-128f")]
    Shake128F = cryptoki_sys::CKP_SLH_DSA_SHAKE_128F,
    #[serde(rename = "CKP_SLH_DSA_SHA2_192S")]
    Sha2_192S = cryptoki_sys::CKP_SLH_DSA_SHA2_192S,
    #[serde(rename = "CKP_SLH_DSA_SHAKE_192S")]
    #[value(name = "shake-192s")]
    Shake192S = cryptoki_sys::CKP_SLH_DSA_SHAKE_192S,
    #[serde(rename = "CKP_SLH_DSA_SHA2_192F")]
    Sha2_192F = cryptoki_sys::CKP_SLH_DSA_SHA2_192F,
    #[serde(rename = "CKP_SLH_DSA_SHAKE_192F")]
    #[value(name = "shake-192f")]
    Shake192F = cryptoki_sys::CKP_SLH_DSA_SHAKE_192F,
    #[serde(rename = "CKP_SLH_DSA_SHA2_256S")]
    Sha2_256S = cryptoki_sys::CKP_SLH_DSA_SHA2_256S,
    #[serde(rename = "CKP_SLH_DSA_SHAKE_256S")]
    #[value(name = "shake-256s")]
    Shake256S = cryptoki_sys::CKP_SLH_DSA_SHAKE_256S,
    #[serde(rename = "CKP_SLH_DSA_SHA2_256F")]
    Sha2_256F = cryptoki_sys::CKP_SLH_DSA_SHA2_256F,
    #[serde(rename = "CKP_SLH_DSA_SHAKE_256F")]
    #[value(name = "shake-256f")]
    Shake256F = cryptoki_sys::CKP_SLH_DSA_SHAKE_256F,
}

impl From<SlhDsaParameterSet> for AttrData {
    fn from(val: SlhDsaParameterSet) -> Self {
        AttrData::Ulong(val.into())
    }
}

impl SlhDsaParameterSet {
    // Object Identifiers for SLH-DSA parameter sets.
    const OID_SLHDSA_SHA2_128S: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 20);
    const OID_SLHDSA_SHA2_128F: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 21);
    const OID_SLHDSA_SHA2_192S: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 22);
    const OID_SLHDSA_SHA2_192F: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 23);
    const OID_SLHDSA_SHA2_256S: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 24);
    const OID_SLHDSA_SHA2_256F: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 25);
    const OID_SLHDSA_SHAKE128S: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 26);
    const OID_SLHDSA_SHAKE128F: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 27);
    const OID_SLHDSA_SHAKE192S: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 28);
    const OID_SLHDSA_SHAKE192F: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 29);
    const OID_SLHDSA_SHAKE256S: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 30);
    const OID_SLHDSA_SHAKE256F: ObjectIdentifier = oid!(2, 16, 840, 1, 101, 3, 4, 3, 31);
}

impl TryFrom<ObjectIdentifier> for SlhDsaParameterSet {
    type Error = SlhDsaError;

    fn try_from(oid: ObjectIdentifier) -> Result<Self, Self::Error> {
        match oid {
            Self::OID_SLHDSA_SHA2_128S => Ok(Self::Sha2_128S),
            Self::OID_SLHDSA_SHA2_128F => Ok(Self::Sha2_128F),
            Self::OID_SLHDSA_SHAKE128S => Ok(Self::Shake128S),
            Self::OID_SLHDSA_SHAKE128F => Ok(Self::Shake128F),
            Self::OID_SLHDSA_SHA2_192S => Ok(Self::Sha2_192S),
            Self::OID_SLHDSA_SHA2_192F => Ok(Self::Sha2_192F),
            Self::OID_SLHDSA_SHAKE192S => Ok(Self::Shake192S),
            Self::OID_SLHDSA_SHAKE192F => Ok(Self::Shake192F),
            Self::OID_SLHDSA_SHA2_256S => Ok(Self::Sha2_256S),
            Self::OID_SLHDSA_SHA2_256F => Ok(Self::Sha2_256F),
            Self::OID_SLHDSA_SHAKE256S => Ok(Self::Shake256S),
            Self::OID_SLHDSA_SHAKE256F => Ok(Self::Shake256F),
            _ => Err(SlhDsaError::BadOid),
        }
    }
}

impl SlhDsaParameterSet {
    const KEY_LENGTH_SLHDSA_128: usize = 32;
    const KEY_LENGTH_SLHDSA_192: usize = 48;
    const KEY_LENGTH_SLHDSA_256: usize = 64;

    /// Public Key length for given parameter set.
    pub fn pk_bytes(parameter_set: Self) -> usize {
        match parameter_set {
            Self::Sha2_128S | Self::Sha2_128F | Self::Shake128S | Self::Shake128F => {
                Self::KEY_LENGTH_SLHDSA_128
            }
            Self::Sha2_192S | Self::Sha2_192F | Self::Shake192S | Self::Shake192F => {
                Self::KEY_LENGTH_SLHDSA_192
            }
            Self::Sha2_256S | Self::Sha2_256F | Self::Shake256S | Self::Shake256F => {
                Self::KEY_LENGTH_SLHDSA_256
            }
        }
    }
}
