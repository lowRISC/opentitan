#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# This script will generate two self signed CA certificates, both using the same
# configuration defined in ca.conf, but signed by different private keys.
# One using the test key file present in the current directory and the other one
# a key stored in Google Cloud KMS.
#
# Signing with Cloud KMS requires the following:
# - a Google KMS integration library
#   (https://github.com/GoogleCloudPlatform/kms-integrations) module
# - a configuration file describing the Cloud KMS project containing the key.
#
# PKCS11_MODULE_PATH and KMS_PKCS11_CONFIG environment variables are set to
# point at these objects. If both variables are present the script attempts to
# generate a Cloud KMS signed certificate.

set -e

cd "$(dirname "$0")"
echo "Generating fake key CA cert ..."
openssl req -new -key raw/sk.pkcs8.der -keyform der \
        -out raw/ca.csr -config ca.conf
openssl x509 -req -in raw/ca.csr -signkey raw/sk.pkcs8.der \
        -keyform der -out raw/ca.pem -days 3650 -extfile ca.conf \
        -extensions v3_ca
echo "Done."

if [[ -z ${KMS_PKCS11_CONFIG} || -z ${PKCS11_MODULE_PATH} ]]; then
  echo "Cloud KMS env not set, skipping Cloud KMS cert generation"
  exit 0
fi
echo "Generating Cloud KMS key CA cert ..."
openssl req -new  -key pkcs11:object=gcs-kms-earlgrey-ze-ca-p256-sha256-key \
          -engine pkcs11 -keyform engine -out ckms/ca.csr -config ca.conf
openssl x509 -req -in ckms/ca.csr  \
        -engine pkcs11 -keyform engine \
        -key pkcs11:object=gcs-kms-earlgrey-ze-ca-p256-sha256-key \
        -out ckms/ca.pem -days 140 -extfile ca.conf -extensions v3_ca
echo "Done."
