// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use serde::{Deserialize, Serialize};
use sha2::Digest;
use std::fmt;
use std::str::FromStr;

use crate::crypto::Error;

#[derive(Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Sha256Digest {
    #[serde(with = "serde_bytes")]
    pub digest: [u8; 32],
}

impl Sha256Digest {
    pub fn hash(data: impl AsRef<[u8]>) -> Self {
        let mut hasher = sha2::Sha256::new();
        hasher.update(data);
        Self {
            digest: hasher.finalize().into(),
        }
    }

    pub fn to_vec(&self) -> Vec<u8> {
        self.digest.to_vec()
    }

    pub fn to_vec_rev(&self) -> Vec<u8> {
        let mut result = self.to_vec();
        result.reverse();
        result
    }
}

impl AsRef<[u8]> for Sha256Digest {
    fn as_ref(&self) -> &[u8] {
        &self.digest
    }
}

impl TryFrom<&[u8]> for Sha256Digest {
    type Error = Error;
    fn try_from(data: &[u8]) -> std::result::Result<Self, Self::Error> {
        Ok(Sha256Digest {
            digest: data
                .try_into()
                .map_err(|_| Error::InvalidHash(hex::encode(data)))?,
        })
    }
}

impl FromStr for Sha256Digest {
    type Err = anyhow::Error;
    fn from_str(s: &str) -> std::result::Result<Self, Self::Err> {
        let s = s.trim_start_matches("0x");
        let data = hex::decode(s)?;
        Ok(Sha256Digest {
            digest: data.try_into().map_err(|_| Error::InvalidHash(s.into()))?,
        })
    }
}

impl fmt::Display for Sha256Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", hex::encode(self))
    }
}

impl fmt::Debug for Sha256Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sha256Digest")
            .field("digest", &self.to_string())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sha256() {
        fn check(msg: &str, digest: &str) {
            assert_eq!(Sha256Digest::hash(msg).to_string(), digest);
        }
        // The digests below can be obtained using `echo -n [msg] | shasum -a 256`.
        // The digest for "abc" is also available at
        // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf
        check(
            "",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        );
        check(
            "abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        );
        check(
            "1111",
            "0ffe1abd1a08215353c233d6e009613e95eec4253832a761af28ff37ac5a150c",
        );
    }
}
