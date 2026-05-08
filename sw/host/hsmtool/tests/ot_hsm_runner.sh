#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail
source sw/host/hsmtool/tests/test_lib.sh

OPENTITANTOOL=sw/host/opentitantool/opentitantool
HSMTOOL=sw/host/hsmtool/hsmtool

# shellcheck disable=SC2206
OTTOOL_ARGS=(${OTTOOL_ARGS})
# shellcheck disable=SC2206
HSMTOOL_ARGS=(${HSMTOOL_ARGS})

if [[ ${PREPARE_CMD+is_set} ]]; then
  # shellcheck disable=SC2206
  PREPARE_CMD=(${PREPARE_CMD})
  run "${PREPARE_CMD[@]}"
fi

if [[ ${FIRST} == "none" ]]; then
  # No operation requested.
  true
elif [[ ${FIRST} == "opentitantool" ]]; then
  run ${OPENTITANTOOL} "${OTTOOL_ARGS[@]}"
  run ${HSMTOOL} "${HSMTOOL_ARGS[@]}"
elif [[ ${FIRST} == "hsmtool" ]]; then
  run ${HSMTOOL} "${HSMTOOL_ARGS[@]}"
  run ${OPENTITANTOOL} "${OTTOOL_ARGS[@]}"
else
  echo "Error: FIRST must be one of 'none, 'opentitantool' or 'hsmtool'" 1>&2
  exit 1
fi
