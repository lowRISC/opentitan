#!/usr/bin/env bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

OPENTITANTOOL=sw/host/opentitantool/opentitantool
TEST_DIR="$(mktemp -d)"
trap 'rm -rf "${TEST_DIR}"' EXIT

# Generate a SPHINCS+ key for export.
run ${HSMTOOL} spx generate --label=test-key --export="${TEST_DIR}/private.pem"

# PEM encoding export -> import roundtrip
run ${HSMTOOL} spx export --label=test-key "${TEST_DIR}/public.pem"
run ${HSMTOOL} spx import --label=import-key "${TEST_DIR}/private.pem"

# Replace keys via `--overwrite`, where we should end up with the overwritten key.
run ${HSMTOOL} spx generate --label=overwrite-key
run ${HSMTOOL} spx generate --label=overwrite-key --overwrite
run ${HSMTOOL} spx import --label=overwrite-key --overwrite "${TEST_DIR}/private.pem"
run ${HSMTOOL} spx export --label=overwrite-key "${TEST_DIR}/overwrite.public.pem"
run cmp "${TEST_DIR}/public.pem" "${TEST_DIR}/overwrite.public.pem"

# Check that the re-imported keys actually remain valid by signing a message.
# Sign with the original and all re-imported private keys, and verify with the
# original and all re-imported public keys (including one passed as an input).
echo "The quick brown fox jumps over the lazy dog" > "${TEST_DIR}/msg.txt"
for sign_key in test-key import-key overwrite-key; do
    run ${HSMTOOL} spx sign --label="${sign_key}" --output="${TEST_DIR}/${sign_key}.sig" \
        "${TEST_DIR}/msg.txt"

    for verify_key in test-key import-key overwrite-key; do
        run ${HSMTOOL} spx verify --label="${verify_key}" "${TEST_DIR}/msg.txt" \
            "${TEST_DIR}/${sign_key}.sig"
    done
    run ${OPENTITANTOOL} --rcfile= spx verify "${TEST_DIR}/public.pem" \
        "${TEST_DIR}/msg.txt" "${TEST_DIR}/${sign_key}.sig"
done
