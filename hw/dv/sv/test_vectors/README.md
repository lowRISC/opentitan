# Test Vectors

## test_vectors_pkg.sv
This class read a list of vector files and parse the useful information to
uvm_sequences.
The following is a list of common properties and methods:
* **_file_list**: A string list of file names grouped by tested functionality.
* **test_vectors_t**: A structure of parsed information.
* **str_to_bytes**: A method to parse string to a vector of bytes.
* **get_test_vectors_path**: A method to get file directory from the run option,
  and concatenate with input file name. Return the full file path.
* **open_file**: A method to open a file with specific path, and return a open
  file handle.
* **parse_sha**: A method to parse SHA vectors files. Return an array of
  test_vectors_t.

## SHA-2 256 vectors
The test vector files inside of `vectors/sha/sha256/` are downloaded from the
[NIST website](https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Secure-Hashing#shavs).

## SHA-2 384 vectors
The test vector files inside of `vectors/sha/sha384/` are downloaded from the
[NIST website](https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Secure-Hashing#shavs).

## SHA-2 512 vectors
The test vector files inside of `vectors/sha/sha512/` are downloaded from the
[NIST website](https://csrc.nist.gov/Projects/Cryptographic-Algorithm-Validation-Program/Secure-Hashing#shavs).

## SHA3 vectors
Test vector files for the 224, 256, 384, and 512 bit variants of SHA3 found at
`vectors/sha/sha3-<224/256/384/512>` are downloaded from the [NIST
website](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip).

## HMAC vectors
Files inside of `vectors/hmac/` contain test vectors extracted from the [NIST website](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/mac/hmactestvectors.zip) for HMAC based on SHA-2 256, 384 and 512.

## SHAKE vectors
Test vector files for the SHA3 Extendable Output Functions in `vectors/xof/shake` are
downloaded from the [NIST
website](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip).

## cSHAKE vectors
Test vectors for the Customizable SHAKE functions are taken from the [NIST
website](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/cSHAKE_samples.pdf).
These vectors are found in `vectors/xof/cshake/`.

## KMAC vectors
Test vectors for KMAC algorithm are taken from NIST website for both the
[XOF](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf)
and
[non-XOF](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMACXOF_samples.pdf)
variants.
These vectors are found in `vectors/xof/kmac/`.

## AES vectors
Test vectors for AES can be found under hw/ip/aes/dv/test_vectors
Test vectors for AES algorithm are taken from the
[NIST website](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/AES_ModesA_All.pdf)
