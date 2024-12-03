# CA Endorsement Keys

Certificate Authority endorsement keys are are used to endorse the following
certificate chains during personalization:
1. DICE attestation certificate chains, and
2. SKU specific certificate chains.

The real (private) keys used for the SIVAL SKU are stored on offline HSMs. The
matching public keys and certificates are checked into the repository.

To use the private keys to endorse the certificates in benchtop provisioning
flow, one must set the following envars:
  - `PKCS11_MODULE_PATH`: to point to the PKCS#11 shared library for the
    hardware token they are using, and
  - `PKCS11_TOKEN_PIN`: to the PIN used for hardware token authentication.

For example, if the SIVAL private keys are stored on a Nitrokey, and you wanted
to test the SIVAL FT provisioning flow, you would issue the following Bazel
command:
```sh
bazel test --test_output=streamed \
  //sw/device/silicon_creator/manuf/base:ft_provision_sival_fpga_hyper310_rom_with_fake_keys \
  --action_env=PKCS11_MODULE_PATH=/opt/nitrokey/lib/libsc-hsm-pkcs11.so \
  --action_env=PKCS11_TOKEN_PIN=<pin>
```

Note: you may also use `opensc-pkcs11.so` for the `PKCS11_MODULE_PATH`. The
debian package `opensc-pkcs11` installs it as
`/usr/lib/x86_64-linux-gnu/opensc-pkcs11.so`.

## Generating a Root CA Certificate from a Token Held ECDSA Key

To generate a Root CA certificate from a public key held on a hardware token,
e.g., Nitrokey, you may use the CSR (Certificate Signing Request) configuration
file checked in to this repo (`dice_ca.conf`) as in input to the following
commands:
```sh
# Set the PKCS11_MODULE_PATH envar to point to the shared library for the
# hardware token you are using, e.g.:
export PKCS11_MODULE_PATH=/opt/nitrokey/lib/libsc-hsm-pkcs11.so

# Generate the CSR:
openssl req -new -engine pkcs11 -keyform engine -config ../dice_ca.conf -out dice_ca.csr \
  -key "pkcs11:pin-value=<pin>;object=sv00-earlgrey-a1-ca-dice-0"

# Generate the X.509 certificate in PEM format:
openssl x509 -req -engine pkcs11 -keyform engine -in dice_ca.csr -out dice_ca.pem \
  -days 3650 -extfile ../dice_ca.conf -extensions v3_ca \
  -signkey "pkcs11:pin-value=694201;object=sv00-earlgrey-a1-ca-dice-0"

# Examine the generated certificate:
openssl x509 -in dice_ca.pem -text
```
