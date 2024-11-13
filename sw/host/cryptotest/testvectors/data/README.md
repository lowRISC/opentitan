# Cryptotest Test Vectors

## AES

### NIST CAVP AES KAT

Source: [NIST CAVP Block Ciphers](https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Block-Ciphers#AES)

We are using the AES KAT Vectors.

## Hash Functions

### NIST CSHAKE Example Values

Source: [NIST Example Values](https://csrc.nist.gov/projects/cryptographic-standards-and-guidelines/example-values) - [file](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/cSHAKE_samples.pdf)

The values were transcribed from the PDF into `cshake_nist_example_values.hjson`.

## ECDSA

### NIST CAVP ECDSA FIPS 186-4 Test Vectors

Source: [NIST CAVP Digital Signatures Page](https://csrc.nist.gov/Projects/cryptographic-algorithm-validation-program/digital-signatures)

We are using the following tests:

- Signature Verification (`SigVer.rsp`)

Unused tests:

- Key Pair Generation (`KeyPair.rsp`): cryptolib does not support key generation for a specified private key
- Public Key Validation Test (`PKV.rsp`): cryptolib does not expose a key validation function
- Signature Generation (`SigGen.txt`): cryptolib does not allow specifying `k`, the per-message secret number.
    - The download also includes `SigGen.rsp` which contains the same test vectors but omits `d` (the private key) and `k`.
