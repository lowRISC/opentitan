#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Test Description:
#
# This tests fuly provisioning an OpenTitan chip by executing both CP and FT
# stages in a single execution of the orchestrator script.

set -ex

cp sw/host/provisioning/orchestrator/src/orchestrator.zip $TEST_TMPDIR

ORCHESTRATOR_PATH=$TEST_TMPDIR/orchestrator.zip

(
  # This script is run by a Bazel sh_test rule, which sets RUNFILES_DIR to point
  # at the test's runfiles. However, if RUNFILES_DIR is set, orchestrator.zip will
  # inherit its value instead of setting it to the proper directory. This breaks
  # runfile resolution, so we unset this variable here.
  unset RUNFILES_DIR

  # Run tool. The path to the --sku-config parameter is relative to the
  # runfiles-dir.
  $PYTHON ${ORCHESTRATOR_PATH} \
    --sku-config=${SKU_CONFIG_PATH} \
    --test-unlock-token="0x11111111_11111111_11111111_11111111" \
    --test-exit-token="0x22222222_22222222_22222222_22222222" \
    --fpga=${FPGA} \
    --non-interactive \
    "$@" \
    --db-path=$TEST_TMPDIR/registry.sqlite
)

# Post-process the coverage profile if coverage mode is enabled.
if [[ "$COVERAGE" == "1" ]]; then
  export COLLECT_CC_COVERAGE="$PWD/$COLLECT_CC_COVERAGE"
  cd "$ROOT"
  "$COLLECT_CC_COVERAGE"
fi
