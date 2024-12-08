# CA Endorsement Keys

Certificate Authority endorsement keys are are used to endorse the following
certificate chains during personalization:
1. DICE attestation certificate chains, and
2. SKU specific certificate chains.

## Fake Keys

The fake keys stored here are used for testing purposes only.
The fake keys have been generated using OpenSSL, and the private portion of
the key has been checked into the repository.

## Real Keys

The real (private) keys used for the SIVAL SKU are stored on offline HSMs.
The matching public keys and certificates are checked into the repository.

To use the private keys to endorse the certificates in benchtop provisioning
flow, one must set the following envars:
  - `PKCS11_MODULE_PATH`: to point to the PKCS#11 shared library for the
    hardware token or HSM they are using, and
  - `PKCS11_TOKEN_PIN`: to the PIN used for hardware token / HSM authentication.

For example, if the SIVAL private keys are stored on a Nitrokey, and you wanted
to test the SIVAL FT provisioning flow, you would issue the following Bazel
command:
```sh
bazel test --test_output=streamed \
  //sw/device/silicon_creator/manuf/base:ft_provision_sival_fpga_hyper310_rom_with_fake_keys \
  --action_env=PKCS11_MODULE_PATH=/opt/nitrokey/lib/libsc-hsm-pkcs11.so \
  --action_env=PKCS11_TOKEN_PIN=123456
```

Note: you may also use `opensc-pkcs11.so` for the `PKCS11_MODULE_PATH`. The
debian package `opensc-pkcs11` installs it as
`/usr/lib/x86_64-linux-gnu/opensc-pkcs11.so`.

# Generating CA Keys and Root Certificates

## Generating fake keys and certificates with OpenSSL
### Generating an ECC P256 Keypair with OpenSSL
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

### Generating a Root CA Certificate

To generate a Root CA certificate using the earlier generated private EC key,
you can use the CSR (Certificate Signing Request) configuration file checked in
to this repo (`dice_ca.conf` or `ext_ca.conf`) as in input to the following
OpenSSL commands:
```sh
# Generate the CSR:
$ openssl req -new -key sk.pem -out dice_ca.csr -config ../dice_ca.conf

# Generate the X.509 certificate in PEM format:
$ openssl x509 -req -in dice_ca.csr -signkey sk.pem -out dice_ca.pem \
    -days 3650 -extfile ../dice_ca.conf -extensions v3_ca

# Examine the generated certificate:
$ openssl x509 -in dice_ca.pem -text
```

## Generating a root CA certificate from a real hardware token held key

To generate a Root CA certificate from a public key held on a hardware token,
e.g., Nitrokey, you may use the CSR (Certificate Signing Request) configuration
file checked in to this repo (`dice_ca.conf`) as in input to the following
commands:
```sh
# Set the PKCS11_MODULE_PATH envar to point to the shared library for the
# hardware token you are using, e.g.:
export PKCS11_MODULE_PATH=/opt/nitrokey/lib/libsc-hsm-pkcs11.so
export HW_TOKEN_PIN=123456

# Generate the CSR:
openssl req -new -engine pkcs11 -keyform engine -config ../dice_ca.conf -out dice_ca.csr \
  -key "pkcs11:pin-value=${HW_TOKEN_PIN};object=sv00-earlgrey-a1-ca-dice-0"

# Generate the X.509 certificate in PEM format:
openssl x509 -req -engine pkcs11 -keyform engine -in dice_ca.csr -out dice_ca.pem \
  -days 3650 -extfile ../dice_ca.conf -extensions v3_ca \
  -signkey "pkcs11:pin-value=${HW_TOKEN_PIN};object=sv00-earlgrey-a1-ca-dice-0"

# Examine the generated certificate:
openssl x509 -in dice_ca.pem -text
```

# Generating the RMA unlock token encryption keypair with OpenSSL

The RMA unlock token encryption keypair is an RSA-3072 key used to encrypt the
RMA unlock token generated during provisioning.

The fake keys (used for testing) in this subdirectory were generated with `openssl`.

```
### Generate the RSA keypair:
$ openssl genrsa -out rma_unlock_enc_rsa3072.pem 3072

### Extract the public key to a separate file:
$ openssl rsa -in rma_unlock_enc_rsa3072.pem -pubout -out rma_unlock_enc_rsa3072.pub.pem

### Convert the PEM files to DER files:
$ openssl rsa -in rma_unlock_enc_rsa3072.pem -outform der -out rma_unlock_enc_rsa3072.der
$ openssl rsa -pubin -in rma_unlock_enc_rsa3072.pub.pem -outform der -out rma_unlock_enc_rsa3072.pub.der
```
