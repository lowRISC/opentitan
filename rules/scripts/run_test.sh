#!/usr/bin/env bash
# echo "<test>"
# echo "<cmd>$@</cmd>"
# echo "<pwd>$PWD</pwd>"
# echo "<env>"
# env
# echo "</env>"
# echo "<output>"
# $@
# echo "</output>"
# echo "</test>"

if [ -z "$OTT_RUN_TEST_OUR_DIR" ]; then
  echo "OTT_RUN_TEST_OUR_DIR not provided, will not log output"
  $@
else
  # variables are documented here:
  # https://bazel.build/reference/test-encyclopedia
  if [ -z "$TEST_RUN_NUMBER" ]; then
    RUN_NR=""
  else
    RUN_NR=".$TEST_RUN_NUMBER"
  fi
  OUT_FILE="$OTT_RUN_TEST_OUR_DIR/$TEST_TARGET$RUN_NR.log"
  mkdir -p $(dirname $OUT_FILE)
  echo "Logging output to $OUT_FILE, see artefact for the log file"
  $@ >$OUT_FILE 2>&1
fi
