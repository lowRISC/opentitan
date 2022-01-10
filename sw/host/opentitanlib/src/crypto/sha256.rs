// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use sha2::Digest;

use crate::util::bigint::fixed_size_bigint;

fixed_size_bigint!(Sha256Digest, at_most 256);

pub fn sha256(data: impl AsRef<[u8]>) -> Sha256Digest {
    let mut hasher = sha2::Sha256::new();
    hasher.update(data);
    Sha256Digest::from_be_bytes(hasher.finalize()).unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sha256() {
        fn check(msg: &str, digest: &str) {
            assert_eq!(sha256(msg.as_bytes()).to_string(), digest);
        }
        // The digests below can be obtained using `echo -n [msg] | shasum -a 256`.
        // The digest for "abc" is also available at
        // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf
        check(
            "",
            "0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        );
        check(
            "abc",
            "0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        );
        check(
            "1111",
            "0x0ffe1abd1a08215353c233d6e009613e95eec4253832a761af28ff37ac5a150c",
        );
    }
}
