#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -uo pipefail
source sw/host/hsmtool/tests/test_lib.sh

shopt -s nocasematch

# Each input key should be a PEM encoded SLH-DSA key, where the algorithm OID
# stored in the ASN.1 object (either a PKCS#8 OneAsymmetricKey or a RFC7468
# SubjectPublicKeyInfo) is a Pre-hash SLH-DSA variant. We test that such keys
# are supported by hsmtool.
index=0
for key in "$@"; do
    ((index++))

    if [ ! -f "$key" ]; then
        echo "Error: $key is not a valid key file."
        exit 1
    fi

    # Check that OpenSSL actually recognizes this key as an SLH-DSA key
    openssl_object_id=$(
        run ${OPENSSL} asn1parse -in "$key" --strictpem \
        | grep -m 1 "OBJECT" \
        | awk -F: '{print $NF}'
    )
    if [[ "$openssl_object_id" != SLH-DSA-SHA*-128s-WITH-SHA* ]]; then
        echo "Error: $key is not recognized as a small 128-bit security HashSLH-DSA key."
        exit 1
    fi

    # Check that hsmtool also recognizes this key as an SLH-DSA key
    hsmtool_output=$(run ${HSMTOOL} slh-dsa import --label="hash-slh-dsa-$index" "$key" 2>&1)
    if [ "$?" -eq 1 ]; then
        if [[ "$hsmtool_output" == *Invalid*Key* ]]; then
            echo "Error: $key is incorrectly recognized as invalid by hsmtool."
        else
            echo "Error: $key produces an unexpected error when given to hsmtool."
        fi
        exit 1
    fi

done

shopt -u nocasematch
