# Cryptotest Test Vectors

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
