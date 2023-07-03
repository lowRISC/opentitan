#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

# This script will run the command line arguments as-is
# and will further save the output to a file if the env
# variable OT_RUN_TEST_OUT_DIR is specified. In this case
# the output log will be $OT_RUN_TEST_OUT_DIR/<path>.log
# where <path> is derived from the bazel test target
# and test run number.
#
# An example usage of this script is as follows:
#
# bazel test \
#   --test_env=OT_RUN_TEST_OUR_DIR=/tmp/log_directory/ \
#   --run_under=//rules/scripts:run_test \
#   //sw/device/silicon_creator/rom/e2e/...
#

if [ -z "$OT_RUN_TEST_OUR_DIR" ]; then
  echo "OT_RUN_TEST_OUR_DIR not provided, will not log output"
  $@
else
  # variables are documented here:
  # https://bazel.build/reference/test-encyclopedia
  if [ -z "$TEST_RUN_NUMBER" ]; then
    RUN_NR=""
  else
    RUN_NR=".$TEST_RUN_NUMBER"
  fi
  OUT_FILE="$OT_RUN_TEST_OUR_DIR/$TEST_TARGET$RUN_NR.log"
  DIRNAME=$(dirname "$OUT_FILE")
  if ! mkdir -p "$DIRNAME"; then
    echo "Could not create "$DIRNAME" to store output log"
    exit 42
  fi
  echo "Logging output to $OUT_FILE"
  # we want to capture the error code here and execute code afterwards
  set +e
  "$@" >"$OUT_FILE" 2>&1
  retn_value=$?
  if ! cat "$OUT_FILE"; then
    echo "Unable to print the output log, something is very wrong"
    exit 43
  fi
  exit $retn_value
fi
