#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -eo pipefail

# Constants

OUTPUT_DIR="$HOME/dev/fuzz_output"
BIN_DIR="$OUTPUT_DIR/bin"
WORK_DIR="$OUTPUT_DIR/workdir"
COVERAGE_REPORT_DIR="$OUTPUT_DIR/coverage_report"

PIPELINE_LOG="$OUTPUT_DIR/pipeline.log"
PIPELINE_ERR_LOG="$OUTPUT_DIR/pipeline_err.log"

CENTIPEDE_BINARY_NAME="centipede"
CENTIPEDE_BINARY_OUT_PATH="$BIN_DIR/$CENTIPEDE_BINARY_NAME"

PROFDATA_PATH="$WORK_DIR/combined_coverage.profdata"

CI_DIR="$(dirname "$(readlink -e "${BASH_SOURCE[0]}")")"
REPO_TOP="$(readlink -e "$CI_DIR/..")"

# TESTS: ROM EXT Boot Services

BOOT_SERVICES_TEST_BINARY_PREFIX="sw/device/silicon_creator/rom_ext"
BOOT_SERVICES_TEST_BINARY_NAME="rom_ext_boot_services_fuzztest_binary"

BOOT_SERVICES_TEST_PREFIX="BootServicesFuzzTest"

BOOT_SERVICES_TESTS=(
  "${BOOT_SERVICES_TEST_PREFIX}.HeaderIdentifier"
  "${BOOT_SERVICES_TEST_PREFIX}.HeaderType"
  "${BOOT_SERVICES_TEST_PREFIX}.HeaderLengthAndDigest"
  "${BOOT_SERVICES_TEST_PREFIX}.EmptyReq"
  "${BOOT_SERVICES_TEST_PREFIX}.EnterRescueReq"
  "${BOOT_SERVICES_TEST_PREFIX}.SetMinimumSecurityVersionReq"
  "${BOOT_SERVICES_TEST_PREFIX}.SetNextBootSlotReq"
  "${BOOT_SERVICES_TEST_PREFIX}.OwnershipUnlockReqRandomMode"
  "${BOOT_SERVICES_TEST_PREFIX}.OwnershipUnlockReqAbortMode"
  "${BOOT_SERVICES_TEST_PREFIX}.OwnershipUnlockReqUpdateMode"
  "${BOOT_SERVICES_TEST_PREFIX}.HandlerNeverCrashesHeader"
  "${BOOT_SERVICES_TEST_PREFIX}.HandlerNeverCrashesMessages"
)

# TESTS: ROM EXT Boot Policy

BOOT_POLICY_TEST_BINARY_PREFIX="sw/device/silicon_creator/rom_ext"
BOOT_POLICY_TEST_BINARY_NAME="rom_ext_boot_policy_fuzztest_binary"

BOOT_POLICY_TEST_PREFIX="BootPolicyFuzzTest"

BOOT_POLICY_TESTS=(
  "${BOOT_POLICY_TEST_PREFIX}.ManifestCheckNeverCrashes"
)

# TESTS: ROM EXT Verify

VERIFY_TEST_BINARY_PREFIX="sw/device/silicon_creator/rom_ext"
VERIFY_TEST_BINARY_NAME="rom_ext_verify_fuzztest_binary"

VERIFY_TEST_PREFIX="VerifyFuzzTest"

VERIFY_TESTS=(
  "${VERIFY_TEST_PREFIX}.VerifyNeverCrashes"
)

# TESTS: Owner Block

OWNER_BLOCK_TEST_BINARY_PREFIX="sw/device/silicon_creator/lib/ownership"
OWNER_BLOCK_TEST_BINARY_NAME="owner_block_fuzztest_binary"

OWNER_BLOCK_TEST_PREFIX="OwnerBlockFuzzTest"

OWNER_BLOCK_TESTS=(
  "${OWNER_BLOCK_TEST_PREFIX}.ParserNeverCrashes"
)

# TESTS: AES Driver Crypto

AES_DRIVER_TEST_BINARY_PREFIX="sw/device/lib/crypto/drivers"
AES_DRIVER_TEST_BINARY_NAME="aes_fuzztest_binary"

AES_DRIVER_TEST_PREFIX="AesDriverFuzzTest"

AES_DRIVER_TESTS=(
  "${AES_DRIVER_TEST_PREFIX}.NeverCrashesEncryptBegin"
  "${AES_DRIVER_TEST_PREFIX}.NeverCrashesDecryptBegin"
)

# TESTS: Perso TLV Data

PERSO_TLV_DATA_TEST_BINARY_PREFIX="sw/device/silicon_creator/manuf/base"
PERSO_TLV_DATA_TEST_BINARY_NAME="perso_tlv_data_fuzztest_binary"

PERSO_TLV_DATA_TEST_PREFIX="PersoTlvDataFuzzTest"

PERSO_TLV_DATA_TESTS=(
  "${PERSO_TLV_DATA_TEST_PREFIX}.GetCertObjNeverCrashes"
  "${PERSO_TLV_DATA_TEST_PREFIX}.CertObjBuildNeverCrashes"
)

# Handle Flags

BUILD_FLAG=false
CLEAN_FLAG=false
FUZZ_FLAG=false
REPORT_FLAG=false
LOG_FLAG=false
TEST_TARGETS=""
NUM_RUNS_PER_TEST=1000
JOB_COUNT=16

while getopts "bcfrlt:n:j:" flag; do
  case $flag in
    b) BUILD_FLAG=true;;
    c) CLEAN_FLAG=true;;
    f) FUZZ_FLAG=true;;
    r) REPORT_FLAG=true;;
    l) LOG_FLAG=true;;
    t) TEST_TARGETS=$OPTARG;; # "boot_services", "boot_policy", "verify", "owner_block", "aes_driver", "perso_tlv_data", or "all"
    n) NUM_RUNS_PER_TEST=$OPTARG;;
    j) JOB_COUNT=$OPTARG;;
    *)
      echo "Unknown Argument: -$OPTARG"
      exit 0
    ;;
  esac
done

if [ "$TEST_TARGETS" = "all" ]; then
  TEST_TARGETS="boot_services,boot_policy,verify,owner_block,aes_driver,perso_tlv_data"
fi

# Ensure output directories exists
mkdir -p $OUTPUT_DIR
mkdir -p $BIN_DIR

if [ $LOG_FLAG == true ]; then
  # Configure Logging
  exec > "$PIPELINE_LOG" 2> "$PIPELINE_ERR_LOG"
fi

echo "Starting Fuzz Pipeline with the following flags:"
echo "* BUILD_FLAG        = $BUILD_FLAG"
echo "* CLEAN_FLAG        = $CLEAN_FLAG"
echo "* FUZZ_FLAG         = $FUZZ_FLAG"
echo "* LOG_FLAG          = $LOG_FLAG"
echo "* REPORT_FLAG       = $REPORT_FLAG"
echo "* TEST_TARGETS      = $TEST_TARGETS"
echo "* NUM_RUNS_PER_TEST = $NUM_RUNS_PER_TEST"
echo "* JOB_COUNT         = $JOB_COUNT"

# Determine which tests to run

declare -A ALIAS_TO_TESTS
declare -A ALIAS_TO_BINARY_NAME
declare -A ALIAS_TO_BINARY_PREFIX

IFS=',' read -ra TEST_TARGETS <<< "$TEST_TARGETS"

for test_target in "${TEST_TARGETS[@]}"; do
  # Determine which test targets to run
  case $test_target in
    "boot_services")
      ALIAS_TO_TESTS["$test_target"]="${BOOT_SERVICES_TESTS[*]}"
      ALIAS_TO_BINARY_PREFIX["$test_target"]="$BOOT_SERVICES_TEST_BINARY_PREFIX"
      ALIAS_TO_BINARY_NAME["$test_target"]="$BOOT_SERVICES_TEST_BINARY_NAME"
    ;;
    "boot_policy")
      ALIAS_TO_TESTS["$test_target"]="${BOOT_POLICY_TESTS[*]}"
      ALIAS_TO_BINARY_PREFIX["$test_target"]="$BOOT_POLICY_TEST_BINARY_PREFIX"
      ALIAS_TO_BINARY_NAME["$test_target"]="$BOOT_POLICY_TEST_BINARY_NAME"
    ;;
    "verify")
      ALIAS_TO_TESTS["$test_target"]="${VERIFY_TESTS[*]}"
      ALIAS_TO_BINARY_PREFIX["$test_target"]="$VERIFY_TEST_BINARY_PREFIX"
      ALIAS_TO_BINARY_NAME["$test_target"]="$VERIFY_TEST_BINARY_NAME"
    ;;
    "owner_block")
      ALIAS_TO_TESTS["$test_target"]="${OWNER_BLOCK_TESTS[*]}"
      ALIAS_TO_BINARY_PREFIX["$test_target"]="$OWNER_BLOCK_TEST_BINARY_PREFIX"
      ALIAS_TO_BINARY_NAME["$test_target"]="$OWNER_BLOCK_TEST_BINARY_NAME"
    ;;
    "aes_driver")
      ALIAS_TO_TESTS["$test_target"]="${AES_DRIVER_TESTS[*]}"
      ALIAS_TO_BINARY_PREFIX["$test_target"]="$AES_DRIVER_TEST_BINARY_PREFIX"
      ALIAS_TO_BINARY_NAME["$test_target"]="$AES_DRIVER_TEST_BINARY_NAME"
    ;;
    "perso_tlv_data")
      ALIAS_TO_TESTS["$test_target"]="${PERSO_TLV_DATA_TESTS[*]}"
      ALIAS_TO_BINARY_PREFIX["$test_target"]="$PERSO_TLV_DATA_TEST_BINARY_PREFIX"
      ALIAS_TO_BINARY_NAME["$test_target"]="$PERSO_TLV_DATA_TEST_BINARY_NAME"
    ;;
    *)
      echo "Unknown Test Target Requested: $test_target"
      exit 0
    ;;
  esac
done

# Move to root of repo
echo "REPO_TOP is $REPO_TOP"
cd "$REPO_TOP"

# Clean old working directory, if requested
if [ $CLEAN_FLAG == true ]; then
  echo "Clearing old workdir data"
  rm -rf $WORK_DIR
fi

# Build binaries, if requested
if [ $BUILD_FLAG == true ]; then
  echo "Removing old binaries"
  rm -rf $CENTIPEDE_BINARY_OUT_PATH

  echo "Building centipede binary"
  bazel build --config=fuzztest-centipede-binary @fuzztest//centipede:$CENTIPEDE_BINARY_NAME
  cp bazel-bin/external/fuzztest\~/centipede/$CENTIPEDE_BINARY_NAME $CENTIPEDE_BINARY_OUT_PATH

  for alias in "${TEST_TARGETS[@]}"; do
    FUZZTEST_BAZEL_NAME="${ALIAS_TO_BINARY_NAME[$alias]}"
    FUZZTEST_BAZEL_PREFIX="${ALIAS_TO_BINARY_PREFIX[$alias]}"
    FUZZTEST_BIN_PATH="$BIN_DIR/$FUZZTEST_BAZEL_NAME"
    FUZZTEST_INSTRUMENTED_BIN_PATH="$BIN_DIR/${FUZZTEST_BAZEL_NAME}_instrumented"

    rm -rf $FUZZTEST_BIN_PATH
    rm -rf $FUZZTEST_INSTRUMENTED_BIN_PATH

    echo "Building fuzzing coverage instrumented fuzz test binary"
    bazel build --config=fuzztest-centipede-binary-fuzzing //$FUZZTEST_BAZEL_PREFIX:$FUZZTEST_BAZEL_NAME
    cp bazel-bin/$FUZZTEST_BAZEL_PREFIX/$FUZZTEST_BAZEL_NAME $FUZZTEST_BIN_PATH

    echo "Building line coverage instrumented fuzz test binary"
    bazel build --config=fuzztest-centipede-binary-instrumented //$FUZZTEST_BAZEL_PREFIX:$FUZZTEST_BAZEL_NAME
    cp bazel-bin/$FUZZTEST_BAZEL_PREFIX/$FUZZTEST_BAZEL_NAME $FUZZTEST_INSTRUMENTED_BIN_PATH
  done
fi

# Verify binaries exist

if [ ! -f "$CENTIPEDE_BINARY_OUT_PATH" ] || [ ! -x "$CENTIPEDE_BINARY_OUT_PATH" ]; then
  echo "Error: File '$CENTIPEDE_BINARY_OUT_PATH' does not exist or is not executable."
  exit 1
fi

for alias in "${TEST_TARGETS[@]}"; do
  FUZZTEST_BAZEL_NAME="${ALIAS_TO_BINARY_NAME[$alias]}"
  FUZZTEST_BAZEL_PREFIX="${ALIAS_TO_BINARY_PREFIX[$alias]}"
  FUZZTEST_BIN_PATH="$BIN_DIR/$FUZZTEST_BAZEL_NAME"
  FUZZTEST_INSTRUMENTED_BIN_PATH="$BIN_DIR/${FUZZTEST_BAZEL_NAME}_instrumented"

  if [ ! -f "$FUZZTEST_BIN_PATH" ] || [ ! -x "$FUZZTEST_BIN_PATH" ]; then
    echo "Error: File '$FUZZTEST_BIN_PATH' does not exist or is not executable."
    exit 1
  fi

  if [ ! -f "$FUZZTEST_INSTRUMENTED_BIN_PATH" ] || [ ! -x "$FUZZTEST_INSTRUMENTED_BIN_PATH" ]; then
    echo "Error: File '$FUZZTEST_INSTRUMENTED_BIN_PATH' does not exist or is not executable."
    exit 1
  fi
done

# Fuzz Testing
if [ $FUZZ_FLAG == true ]; then
  echo "Start: Fuzz Testing"

  echo "Start: Fuzz Testing"

  for alias in "${TEST_TARGETS[@]}"; do
    FUZZTEST_BIN_NAME="${ALIAS_TO_BINARY_NAME[$alias]}"
    FUZZTEST_BIN_PATH="$BIN_DIR/$FUZZTEST_BIN_NAME"
    FUZZTEST_INSTRUMENTED_BIN_PATH="$BIN_DIR/${FUZZTEST_BIN_NAME}_instrumented"

   read -ra tests_for_binary <<< "${ALIAS_TO_TESTS[$alias]}"

    echo "Running fuzz tests for binary: $FUZZTEST_BIN_NAME"

    for test_name in "${tests_for_binary[@]}"; do
      "$CENTIPEDE_BINARY_OUT_PATH" --workdir="$WORK_DIR/$test_name" \
        --binary="$FUZZTEST_BIN_PATH --fuzz=$test_name --corpus_database=" \
        --clang_coverage_binary="$FUZZTEST_INSTRUMENTED_BIN_PATH --fuzz=$test_name --corpus_database=" \
        --num_runs="$NUM_RUNS_PER_TEST" \
        --num_threads="$JOB_COUNT" \
        --total_shards="$JOB_COUNT" \
        --first_shard_index=0
    done

  done

  echo "End: Fuzz Testing"
fi

# Coverage Report Generation
# TODO: This isn't an ideal solution if multiple test targets are used.
# A different method would be needed to aggregate coverage data across multiple
# binaries and visualize it together. Right now, HTML reports are generated on a
# per binary basis.
if [ $REPORT_FLAG == true ]; then
  echo "Start: Creating Coverage Report"

  echo "Aggregating all .profraw files and running llvm-profdata merge"
  find $WORK_DIR -name "*.profraw" -print0 | xargs -0 llvm-profdata merge -o $PROFDATA_PATH -sparse

  for binary_name in "${ALIAS_TO_BINARY_NAME[@]}"; do
    echo "Running llvm-cov show to generate HTML report for $binary_name"

    instrumented_binary="$BIN_DIR/${binary_name}_instrumented"

    llvm-cov show -format=html -output-dir="$COVERAGE_REPORT_DIR/$binary_name" \
      -instr-profile=$PROFDATA_PATH \
      --ignore-filename-regex="external/.*" \
      --ignore-filename-regex="bazel-out/.*" \
      "$instrumented_binary"
  done

  echo "End: Creating Coverage Report"
fi
