#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -uo pipefail
source sw/host/hsmtool/tests/test_lib.sh

shopt -s nocasematch

# Usage: hash_slh_dsa_key_test.sh <private key> <public key>
#
# Each input key should be a PEM-encoded SLH-DSA key, where the algorithm OID
# stored in the ASN.1 object (either a PKCS#8 `OneAsymmetricKey` or an
# RFC 5280 `SubjectPublicKeyInfo`) is a Pre-Hash SLH-DSA variant. We test
# that such keys are supported by hsmtool.
if [ "$#" -ne 2 ]; then
    echo "Usage: $0 <private key> <public key>"
    exit 1
fi

function check_key() {
    local key="$1"
    local label="$2"
    shift 2

    if [ ! -f "$key" ]; then
        echo "Error: $key is not a valid key file."
        exit 1
    fi

    # Check that OpenSSL actually recognizes this key as an SLH-DSA key.
    # Current OpenSSL (3.5) at the time of writing does not support
    # Pre-Hash mode SLH-DSA signing & verification, so this is the limit
    # of what we can test for now.
    echo "${OPENSSL} asn1parse -in $key -strictpem"
    local openssl_object_id
    openssl_object_id=$(
        "${OPENSSL}" asn1parse -in "$key" -strictpem \
        | grep -m 1 "OBJECT" \
        | awk -F: '{print $NF}'
    )
    if [[ "$openssl_object_id" != SLH-DSA-SHA*-128s-WITH-SHA* ]]; then
        echo "Error: $key is not recognized as a small 128-bit security HashSLH-DSA key."
        exit 1
    fi

    # Check that hsmtool also recognizes this key as an SLH-DSA key
    #
    # FIXME: hsmtool currently does not recognize the HashSLH-DSA algorithm
    # identifiers (OIDs) in the PKCS#8/SPKI ASN.1 encodings, despite the fact
    # that it supports use of the underlying `CKM_HASH_SLH_DSA` mechanism type.
    # To test the OpenSSL parsing in CI, this test is marked as not broken
    # and tests the inverse (that hsmtool does *not* recognize the algorithm).
    local hsmtool_args=(slh-dsa import --label="$label" "$@" "$key")
    echo "${HSMTOOL} ${hsmtool_args[*]}"
    local hsmtool_output
    if hsmtool_output=$("${HSMTOOL}" "${hsmtool_args[@]}" 2>&1); then
        echo "$hsmtool_output"
        if [[ "$hsmtool_output" == *Invalid*Key* ]]; then
            echo "Error: $key is incorrectly recognized as invalid by hsmtool."
        else
            echo "Error: $key produces an unexpected error when given to hsmtool."
            exit 1
        fi
    fi
}

check_key "$1" "hash-slh-dsa-private"
check_key "$2" "hash-slh-dsa-public" --public
