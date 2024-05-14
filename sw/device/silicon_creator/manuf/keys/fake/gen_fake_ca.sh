#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# This script will generate two self signed CA certificates, both using the same
# configuration defined in fake_ca.conf, but signed by different private keys.
# One using the test key file present in the current directory and the other one
# a key stored in Google Cloud KMS.
#
# Signing with Cloud KMS requires the following:
# - a Google KMS integration  library
#   (https://github.com/GoogleCloudPlatform/kms-integrations) module
# - a configuration file describing the Cloud KMS project containing the key.
#
# PKCS11_MODULE_PATH and KMS_PKCS11_CONFIG environment variables are set to
# point at these objects. If both variables are present the script attempts to
# generate a Cloud KMS signed certificate.
#
# The generated certificates are named fake_ca and ckms_ca and are saved in both
# DER and PEM forms, certificate file names are printed by this script upon
# successful certificate generation.

set -e

pem_to_der() {
  local pem_name="${1}"
  local der_name="${pem_name/.pem/.der}"

  openssl x509 -in "${pem_name}" -outform der -out "${der_name}"
  cert=$(readlink -f "${pem_name}" | sed 's/pem/{pem,der}/')
  echo "*****Self signed CA saved in ${cert}"
  echo
}

cd "$(dirname "$0")"
echo "generating fake key CA cert"
openssl req -new -key  cert_endorsement_key.sk.der -keyform der \
        -out fake_ca.csr -config fake_ca.conf
openssl x509 -req -in fake_ca.csr -signkey cert_endorsement_key.sk.der \
        -keyform der -out fake_ca.pem -days 3650 -extfile fake_ca.conf \
        -extensions v3_ca
pem_to_der fake_ca.pem

if [[ -z ${KMS_PKCS11_CONFIG} || -z ${PKCS11_MODULE_PATH} ]]; then
  echo "Cloud KMS env not set, skipping Cloud KMS cert generation"
  exit 0
fi
echo "generating Cloud KMS key CA cert"
openssl req -new  -key pkcs11:object=gcs-kms-earlgrey-ze-ca-p256-sha256-key \
          -engine pkcs11 -keyform engine  -out ckms_ca.csr -config fake_ca.conf
openssl x509 -req -in ckms_ca.csr  \
        -engine pkcs11 -keyform engine \
        -key pkcs11:object=gcs-kms-earlgrey-ze-ca-p256-sha256-key \
        -out ckms_ca.pem -days 140 -extfile fake_ca.conf -extensions v3_ca
pem_to_der ckms_ca.pem
