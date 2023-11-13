# Host Manufacturing ECC Keys

Host manufacturing ECC keys are used to generate a shared AES key for exporting the RMA unlock token during device personalization.
The fake keys stored here are used for testing purposes only (see the `personalize_functest` in `sw/device/silicon_creator/manuf/lib/`.
These fake keys have been generated using OpenSSL, and the private portion of the key has been checked into the repository.
Tests can reference this key file, and use it to derive the associated public key on the fly.

# Generating Additional Keys with OpenSSL

To generate additional fake keys for testing using OpenSSL, follow these steps:
```sh
# Generate the curve:
openssl ecparam -out curve.pem -name prime256v1

# Generate the ECC private key:
openssl ecparam -in curve.pem -genkey -out sk_hsm.pem

# Convert the ECC private key from SEC1 format to PKCS8 (we do this because
# the Rust elliptic-curve crate is able to load PKCS8 keys with less additional
# crates):
openssl pkcs8 -in sk_hsm.pem -topk8 -nocrypt -out sk_hsm.pkcs8.der -outform DER

# Show the ECC public key (not required, but helps confirm the above worked):
openssl ec -in sk_hsm.pem -text -noout
```
