#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

PARAM="${1:-mldsa-87}"
DATA="${2:-sw/host/hsmtool/tests/tqbf.txt}"
LABEL="test_mldsa_$(date +%s)_$RANDOM"

SIGNATURE="$(mktemp)"
PUBKEY="$(mktemp)"
trap 'rm -f "$SIGNATURE" "$PUBKEY"' EXIT

echo "Generating ML-DSA key with parameter set ${PARAM}..."
run "${HSMTOOL}" mldsa generate --label "${LABEL}" --parameter-set "${PARAM}"

echo "Exporting ML-DSA public key..."
run "${HSMTOOL}" mldsa export --label "${LABEL}" --format pem "${PUBKEY}"

echo "Signing data with ML-DSA..."
run "${HSMTOOL}" mldsa sign --label "${LABEL}" --output "${SIGNATURE}" "${DATA}"

echo "Verifying ML-DSA signature with hsmtool..."
run "${HSMTOOL}" mldsa verify --label "${LABEL}" "${SIGNATURE}" "${DATA}"

: "${OPENSSL:?OPENSSL environment variable must be set}"

echo "Cross-verifying ML-DSA signature with OpenSSL..."
"${OPENSSL}" pkeyutl -verify -pubin -inkey "${PUBKEY}" -rawin -in "${DATA}" -sigfile "${SIGNATURE}"

echo "ML-DSA test passed successfully for ${PARAM}!"
