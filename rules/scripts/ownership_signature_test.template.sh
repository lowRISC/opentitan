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
ECDSA_SIG=@ECDSA_SIG@
SPX_SIG=@SPX_SIG@
KEY_ARGS=()
RESULT_STATUS=0

echo "___Starting ownership verification___"

# If ECDSA key is provided, include it in the verify command
if [[ ! -z "$ECDSA_KEY" ]]; then
  KEY_ARGS+=("--ecdsa-pub-key=${ECDSA_KEY}")
fi

# If SPX key is provided, include it in the verify command
if [[ ! -z "$SPX_KEY" ]]; then
  KEY_ARGS+=("--spx-pub-key=${SPX_KEY}")
fi

# If ECDSA signature is provided, include it in the verify command
if [[ ! -z "$ECDSA_SIG" ]]; then
  VERIFY_ARGS+=("--ecdsa-sig=${ECDSA_SIG}")
fi

# If SPX signature is provided, include it in the verify command
if [[ ! -z "$SPX_SIG" ]]; then
  VERIFY_ARGS+=("--spx-sig=${SPX_SIG}")
fi

for file in "${FILES_TO_CHECK[@]}"
do
  echo -n "Checking signature of ${file} (with embedded keys)..."

  # TEST 1: Ownership Verify without overriding public keys (extracts from config)
  ${OPENTITANTOOL} --rcfile= ownership verify "${VERIFY_ARGS[@]}" ${file}

  if [[ $? -eq 0 ]]; then
    echo "ok."
  else
    echo "failed."
    RESULT_STATUS=1
  fi

  if [[ ${#KEY_ARGS[@]} -ne 0 ]]; then
    echo -n "Checking signature of ${file} (with explicit keys)..."

    # TEST 2: Ownership Verify with explicit keys provided
    ${OPENTITANTOOL} --rcfile= ownership verify "${KEY_ARGS[@]}" "${VERIFY_ARGS[@]}" ${file}

    if [[ $? -eq 0 ]]; then
      echo "ok."
    else
      echo "failed."
      RESULT_STATUS=1
    fi
  fi
done

# If this is a negative test, invert the result status
if [[ "$IS_NEGATIVE_TEST" == "True" ]]; then
  echo "Negative test, inverting result status."
  RESULT_STATUS=$((1 - $RESULT_STATUS))
fi

echo "Status: $RESULT_STATUS"

exit $RESULT_STATUS
