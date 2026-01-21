#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -o pipefail

FILES_TO_CHECK=(@FILES@)

IS_NEGATIVE_TEST=@IS_NEGATIVE_TEST@
OPENTITANTOOL=@OPENTITANTOOL@
VERIFY_ARGS=(@VERIFY_ARGS@)
ECDSA_KEY=@ECDSA_KEY@
SPX_KEY=@SPX_KEY@
KEY_ARGS=()
RESULT_STATUS=0

echo "___Starting signature verification & manifest key verification___"

# If ECDSA key is provided, include it in the manifest update
if [[ ! -z "$ECDSA_KEY" ]]; then
  KEY_ARGS+=("--ecdsa-key=${ECDSA_KEY}")
fi

# If SPX key is provided, include it in the manifest update
if [[ ! -z "$SPX_KEY" ]]; then
  KEY_ARGS+=("--spx-key=${SPX_KEY}")
fi

for file in "${FILES_TO_CHECK[@]}"
do
  # TEST 1: ECDSA key and/or SPX key integrity
  # If there are keys to verify, perform manifest update
  if [[ ${#KEY_ARGS[@]} -ne 0 ]]; then
    echo -n "Checking key material in ${file}..."
        # We process the original file through the tool to ensure it has the
        # same serialization (e.g. null extension handling) as the version
        # with updated public keys we are about to generate.
        ${OPENTITANTOOL}  --rcfile= image manifest update \
          --private-keys-sign=false \
          --output=/tmp/manifest_test_original.$$ \
          ${file}
        ${OPENTITANTOOL}  --rcfile= image manifest update \
          --private-keys-sign=false \
          "${KEY_ARGS[@]}" \
          --output=/tmp/manifest_test_key_verify.$$ \
          ${file}

    cmp /tmp/manifest_test_original.$$ /tmp/manifest_test_key_verify.$$

    if [[ $? -eq 0 ]]; then
      echo "ok."
    else
      echo "failed."
      RESULT_STATUS=1
    fi
  fi

  echo -n "Checking signature of ${file}..."

  # TEST 2: Signature verification
  ${OPENTITANTOOL} --rcfile= image manifest verify "${VERIFY_ARGS[@]}" ${file}

  if [[ $? -eq 0 ]]; then
    echo "ok."
  else
    echo "failed."
    RESULT_STATUS=1
  fi
done

# If this is a negative test, invert the result status
if [[ "$IS_NEGATIVE_TEST" == "True" ]]; then
  echo "Negative test, inverting result status."
  RESULT_STATUS=$((1 - $RESULT_STATUS))
fi

echo "Status: $RESULT_STATUS"

exit $RESULT_STATUS
