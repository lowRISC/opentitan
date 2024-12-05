# CA Endorsement Keys

Certificate Authority endorsement keys are are used to endorse the following
certificate chains during personalization:
1. DICE attestation certificate chains, and
2. SKU specific certificate chains.

The fake keys stored here are used for testing purposes only.
These fake keys have been generated using OpenSSL, and the private portion of
the key has been checked into the repository.

# Generating CA Keys and a Root Certificate with OpenSSL

## Generating an ECC P256 Keypair with OpenSSL
To generate additional fake keys for testing using OpenSSL, follow these steps:
```sh
# Generate the curve:
$ openssl ecparam -out curve.pem -name prime256v1

# Generate the ECC private key in SEC1 PEM format:
$ openssl ecparam -in curve.pem -genkey -out sk.pem

# Convert the ECC private key from SEC1 format to PKCS8 (we do this because
# the Rust elliptic-curve crate is able to load PKCS8 keys with less additional
# crates):
$ openssl pkcs8 -in sk.pem -topk8 -nocrypt -out sk.pkcs8.der -outform DER

# Show the ECC public key (not required, but helps confirm the above worked):
$ openssl ec -in sk.pem -text -noout
```

## Generating a Root CA Certificate

To generate a Root CA certificate using the earlier generated private EC key,
you can use the CSR (Certificate Signing Request) configuration file checked in
to this directory (`ca.conf`) as in input to the following OpenSSL commands:
```sh
# Generate the CSR:
$ openssl req -new -key sk.pem -out ca.csr -config ca.conf

# Generate the X.509 certificate in PEM format:
$ openssl x509 -req -in ca.csr -signkey sk.pem -out ca.pem -days 3650 \
    -extfile ca.conf -extensions v3_ca

# Examine the generated certificate:
$ openssl x509 -in ca.pem -text
```
