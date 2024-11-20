#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# This script will generate two self signed CA certificates, each using a
# different configuration, but signed by the same (fake) private keys. These
# root CA certificates may be used for testing perso flows on the FPGA.

set -e

cd "$(dirname "$0")"

DICE_CA_KEY="sk.pkcs8.der"
EXT_CA_KEY="$DICE_CA_KEY"

echo "Generating fake key DICE CA cert ..."
openssl req -new -key "$DICE_CA_KEY" -keyform der \
        -out dice_ca.csr -config dice_ca.conf
openssl x509 -req -in dice_ca.csr -signkey "$DICE_CA_KEY" \
        -keyform der -out dice_ca.pem -days 3650 -extfile dice_ca.conf \
        -extensions v3_ca
echo "Done."

echo "Generating fake key Personalization Extension CA cert ..."
openssl req -new -key "$EXT_CA_KEY" -keyform der \
        -out ext_ca.csr -config ext_ca.conf
openssl x509 -req -in ext_ca.csr -signkey "$EXT_CA_KEY"  \
        -keyform der -out ext_ca.pem -days 3650 -extfile ext_ca.conf \
        -extensions v3_ca
echo "Done."
