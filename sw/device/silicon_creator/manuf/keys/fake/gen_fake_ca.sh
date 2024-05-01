#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script will generate a self signed CA certificate using the configuration
# and private key files present in the same directory.
#
# The generated certificate is saved in both DER and PEM forms, file names are
# printed by this script on successful completion.

set -e

cd "$(dirname "$0")"
openssl req -new -key  cert_endorsement_key.sk.der -keyform der \
   -out fake_ca.csr -config fake_ca.conf
openssl x509 -req -in fake_ca.csr -signkey cert_endorsement_key.sk.der \
   -keyform der -out fake_ca.pem -days 3650 -extfile fake_ca.conf \
   -extensions v3_ca
openssl x509 -in fake_ca.pem -outform der -out fake_ca.der
echo
cert=$(readlink -f fake_ca.pem | sed 's/pem/{pem,der}/')
echo "Self signed CA saved in ${cert}"
