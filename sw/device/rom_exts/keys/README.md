# Introduction

The main idea of the development key pair and other signing artefacts is to
make cross-development of on device and host side components for ROM_EXT
signing easier.

It is also useful when starting new development, as it is easier to make sure
that signing process is correct by matching the produced  hashes and signatures
against the reference files provided.

Typical use-case would be - signing ROM_EXT image via host side tooling, and
then using the same key pair on device to validate the signature.

Files breakdown:
- `test_key_private.pem`      : private key (DER encoded binary) in PEM
                                representation.
- `test_key_public.pem`       : public key (DER encoded binary) in PEM
                                representation.
`testing` sub-directory:
- `hello_world.bin`           : reference file containing "Hello World!".
- `hello_world_digest.base64` : SHA-256 digest in base64 representation.
- `hello_world.sign.base64`   : RSASSA-PKCS1-V1_5-SIGN signature (DER encoded
                                binary) in base64 representation.

** Please note that some tools/libraries require files in DER binary encoding.
Instructions below include commands to generate DER keys and signature
artifacts. **

# Keys

This guide assumes that commands are run from within `sw/device/rom_exts/keys`
directory.

`cd sw/device/rom_exts/keys`

## How the key pair was generated?

```
// Private RSA key in `.pem` and `.der` representations.
openssl genrsa -3 -out test_key_private.pem 3072
openssl rsa -in test_key_private.pem -outform DER -out test_key_private.der
```

```
// Public RSA key in `.pem` and `.der` representations.
openssl rsa -in test_key_private.pem -pubout -out test_key_public.pem
openssl rsa                \
  -in test_key_private.pem \
  -outform DER -pubout     \
  -out test_key_public.der
```

# Hash, signature generation and verification.

This guide assumes that commands are run from within
`sw/device/rom_exts/keys/testing` directory.

`cd sw/device/rom_exts/keys/testing`

## How the reference file was signed?

```
// Hash generation.
openssl dgst -sha256 -binary -out hello_world_digest.bin hello_world.bin

// Convert hash from binary to base64.
openssl base64 -in hello_world_digest.bin -out hello_world_digest.base64

// Convert hash from base64 to binary.
openssl base64 -d -in hello_world_digest.base64 -out hello_world_digest.bin
```

```
// RSASSA-PKCS1-V1_5-SIGN.
// For DER use `-keyform DER` and `-inkey ../test_key_private.der`.
openssl pkeyutl                   \
  -keyform PEM                    \
  -inkey ../test_key_private.pem  \
  -pkeyopt rsa_padding_mode:pkcs1 \
  -pkeyopt digest:sha256          \
  -in hello_world_digest.bin      \
  -out hello_world.sign -sign
```

```
// Convert the signature from binary to base64.
openssl base64 -in hello_world.sign -out hello_world.sign.base64

// Convert the signature from base64 to binary.
openssl base64 -d -in hello_world.sign.base64 -out hello_world.sign
```

## Signature verification.

```
// From source.
openssl dgst                     \
  -sha256                        \
  -verify ../test_key_public.pem \
  -signature hello_world.sign    \
  hello_world.bin
```

```
// From hash.
openssl pkeyutl                  \
  -verify                        \
  -in hello_world_digest.bin     \
  -sigfile hello_world.sign      \
  -pkeyopt digest:sha256         \
  -inkey ../test_key_private.pem
```
