// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use crate::MldsaError;
use ml_dsa::common::getrandom::SysRng;
use ml_dsa::{
    EncodedSignature, EncodedVerifyingKey, ExpandedSigningKeyBytes, MlDsa44, MlDsa65, MlDsa87,
    MlDsaParams, Seed, SigningKey,
};
use pkcs8::ObjectIdentifier;
use pkcs8::spki::AssociatedAlgorithmIdentifier;
use std::mem::size_of;
use strum::{Display, EnumString};

/// Maximum length of the context string (FIPS 204).
pub(crate) const MAX_CONTEXT_LEN: usize = 255;

/// ML-DSA parameter sets (FIPS 204).
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, EnumString, Display)]
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
    /// All parameter sets.
    pub const ALL: &[MldsaParameterSet] = &[Self::Mldsa44, Self::Mldsa65, Self::Mldsa87];

    /// Returns the object identifier of the parameter set (RFC 9881).
    pub const fn oid(&self) -> ObjectIdentifier {
        match *self {
            Self::Mldsa44 => MlDsa44::ALGORITHM_IDENTIFIER.oid,
            Self::Mldsa65 => MlDsa65::ALGORITHM_IDENTIFIER.oid,
            Self::Mldsa87 => MlDsa87::ALGORITHM_IDENTIFIER.oid,
        }
    }

    /// Returns the parameter set with the given object identifier.
    pub fn from_oid(oid: ObjectIdentifier) -> Option<Self> {
        Self::ALL.iter().copied().find(|p| p.oid() == oid)
    }

    /// Returns the length of a public key in bytes.
    pub const fn public_key_len(&self) -> usize {
        match *self {
            Self::Mldsa44 => size_of::<EncodedVerifyingKey<MlDsa44>>(),
            Self::Mldsa65 => size_of::<EncodedVerifyingKey<MlDsa65>>(),
            Self::Mldsa87 => size_of::<EncodedVerifyingKey<MlDsa87>>(),
        }
    }

    /// Returns the length of a signature in bytes.
    pub const fn signature_len(&self) -> usize {
        match *self {
            Self::Mldsa44 => size_of::<EncodedSignature<MlDsa44>>(),
            Self::Mldsa65 => size_of::<EncodedSignature<MlDsa65>>(),
            Self::Mldsa87 => size_of::<EncodedSignature<MlDsa87>>(),
        }
    }

    /// Derives the encoded public key from `seed`.
    pub(crate) fn public_key(&self, seed: &Seed) -> Vec<u8> {
        match *self {
            Self::Mldsa44 => public_key::<MlDsa44>(seed),
            Self::Mldsa65 => public_key::<MlDsa65>(seed),
            Self::Mldsa87 => public_key::<MlDsa87>(seed),
        }
    }

    /// Derives the encoded expanded secret key from `seed`.
    pub(crate) fn expanded_key(&self, seed: &Seed) -> zeroize::Zeroizing<Vec<u8>> {
        match *self {
            Self::Mldsa44 => expanded_key::<MlDsa44>(seed),
            Self::Mldsa65 => expanded_key::<MlDsa65>(seed),
            Self::Mldsa87 => expanded_key::<MlDsa87>(seed),
        }
    }

    /// Signs `msg` under `context` with the key derived from `seed` (pure mode).
    pub(crate) fn sign(
        &self,
        seed: &Seed,
        context: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, MldsaError> {
        if context.len() > MAX_CONTEXT_LEN {
            return Err(MldsaError::BadContextLength(context.len()));
        }
        match *self {
            Self::Mldsa44 => sign::<MlDsa44>(seed, context, msg),
            Self::Mldsa65 => sign::<MlDsa65>(seed, context, msg),
            Self::Mldsa87 => sign::<MlDsa87>(seed, context, msg),
        }
    }
}

fn public_key<P: MlDsaParams>(seed: &Seed) -> Vec<u8> {
    SigningKey::<P>::from_seed(seed)
        .expanded_key()
        .verifying_key()
        .encode()
        .to_vec()
}

fn expanded_key<P: MlDsaParams>(seed: &Seed) -> zeroize::Zeroizing<Vec<u8>> {
    // The expanded encoding is deprecated in favour of the seed, but it is
    // still needed to check keys that carry both.
    #[allow(deprecated)]
    let mut expanded: ExpandedSigningKeyBytes<P> = SigningKey::<P>::from_seed(seed)
        .expanded_key()
        .to_expanded();
    let key = zeroize::Zeroizing::new(expanded.to_vec());
    zeroize::Zeroize::zeroize(expanded.as_mut_slice());
    key
}

fn sign<P: MlDsaParams>(seed: &Seed, context: &[u8], msg: &[u8]) -> Result<Vec<u8>, MldsaError> {
    let signature = SigningKey::<P>::from_seed(seed)
        .expanded_key()
        .sign_randomized(msg, context, &mut SysRng)
        .map_err(|_| MldsaError::SigGen)?;
    Ok(signature.encode().to_vec())
}

#[cfg(test)]
mod test {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn parameters() {
        let params = MldsaParameterSet::Mldsa87;
        assert_eq!(params.public_key_len(), 2592);
        assert_eq!(params.signature_len(), 4627);
        assert_eq!(MldsaParameterSet::from_oid(params.oid()), Some(params));
        assert_eq!(MldsaParameterSet::from_str(&params.to_string()), Ok(params));
        assert_eq!(MldsaParameterSet::from_str("ml-dsa-87"), Ok(params));
    }
}
