#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# This script will simply execute the command line and,
# if $OTT_RUN_TEST_OUR_DIR is defined, will log the output to a file.
# This script assumes that it is run in the "bazel test" environment
# so that $TEST_TARGET (and optionally $TEST_RUN_NUMBER is tests are run
# several times) is defined.

if [ -z "$OTT_RUN_TEST_OUR_DIR" ]; then
  echo "OTT_RUN_TEST_OUR_DIR not provided, will not log output"
  "$@"
else
  # variables are documented here:
  # https://bazel.build/reference/test-encyclopedia
  if [ -z "$TEST_RUN_NUMBER" ]; then
    RUN_NR=""
  else
    RUN_NR=".$TEST_RUN_NUMBER"
  fi
  OUT_FILE="$OTT_RUN_TEST_OUR_DIR/$TEST_TARGET$RUN_NR.log"
  mkdir -p "$(dirname $OUT_FILE)"
  echo "Logging output to $OUT_FILE, see artefact for the log file"
  "$@" >"$OUT_FILE" 2>&1
  # print file *after* the run
  cat "$OUT_FILE"
fi
