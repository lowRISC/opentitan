#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

KEYTYPE="$1"
TEST_DIR="$(mktemp -d)"
trap 'rm -rf "${TEST_DIR}"' EXIT

# Generate a key which can be exported both normally and wrapped.
run ${HSMTOOL} "${KEYTYPE}" generate --label=test-key \
    --private-template='{"CKA_EXTRACTABLE": true, "CKA_SENSITIVE": false}'

# Generate an AES key for wrapping
run ${HSMTOOL} aes generate --label=wrap-key

# Public/Private key PEM & DER exports -> import roundtrips.
for format in pem der; do
    run ${HSMTOOL} "${KEYTYPE}" export --label=test-key --format="${format}" \
        "${TEST_DIR}/public.${format}"
    run ${HSMTOOL} "${KEYTYPE}" export --label=test-key --private --format="${format}" \
        "${TEST_DIR}/private.${format}"
    run ${HSMTOOL} "${KEYTYPE}" import --label="test-public-${format}" --public \
        "${TEST_DIR}/public.${format}"
    run ${HSMTOOL} "${KEYTYPE}" import --label="test-private-${format}" \
        "${TEST_DIR}/private.${format}"
done

# Wrapped key export -> import roundtrip.
run ${HSMTOOL} "${KEYTYPE}" export --label=test-key --private --wrap=wrap-key \
    "${TEST_DIR}/private.wrapped"
run ${HSMTOOL} "${KEYTYPE}" import --label=test-private-wrapped --unwrap=wrap-key \
    "${TEST_DIR}/private.wrapped"

# Check that the re-imported keys actually remain valid by signing a message.
# Sign with the original and all re-imported private keys, and verify with the
# original and all re-imported public keys.
echo "The quick brown fox jumps over the lazy dog" > "${TEST_DIR}/msg.txt"
for sign_key in test-key test-private-pem test-private-der test-private-wrapped; do
    run ${HSMTOOL} "${KEYTYPE}" sign --label="${sign_key}" --format=plain-text \
        --output="${TEST_DIR}/${sign_key}.sig" "${TEST_DIR}/msg.txt"

    for verify_key in test-key test-public-pem test-public-der; do
        run ${HSMTOOL} "${KEYTYPE}" verify --label="${verify_key}" --format=plain-text \
            "${TEST_DIR}/msg.txt" "${TEST_DIR}/${sign_key}.sig"
    done
done
