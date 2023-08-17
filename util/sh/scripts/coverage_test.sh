#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source util/sh/lib/strict.sh
source util/sh/lib/log.sh
source util/sh/lib/error.sh
source util/sh/lib/traps.sh

readonly BAZEL="./bazelisk.sh"
readonly BITSTREAM_TARGET="//hw/bitstream:gcp_spliced_test_rom"
readonly WORKSPACE_PATH
WORKSPACE_PATH=$(${BAZEL} info workspace)
readonly BITSTREAM_PATH
BITSTREAM_PATH=${WORKSPACE_PATH}/$(${BAZEL} cquery --output=starlark --starlark:expr "target.files.to_list()[0].path" "${BITSTREAM_TARGET}")
readonly COVERAGE_TEST_TARGET="//sw/device/tests:coverage_test_fpga_cw310_test_rom"
readonly COVERAGE_TEST_LOG
COVERAGE_TEST_LOG="$(${BAZEL} info bazel-testlogs)/sw/device/tests/coverage_test_fpga_cw310_test_rom/test.log"

# Build and program bitstream with uninstrumented ROM
log "Bitstream target: ${BITSTREAM_TARGET}"
log "Bitstream path: ${BITSTREAM_PATH}"
log "Building bitstream..."
${BAZEL} build "${BITSTREAM_TARGET}"
log "Programming the FPGA..."
${BAZEL} run //sw/host/opentitantool -- --uarts=/dev/opentitan/cw_310_uart_0,/dev/opentitan/cw_310_uart_1 fpga load-bitstream "${BITSTREAM_PATH}"
# Measure coverage
log "Measuring coverage..."
${BAZEL} coverage --define bitstream=skip --test_output=streamed --config=ot_coverage_on_target "${COVERAGE_TEST_TARGET}"
# Check log
log "Test log: ${COVERAGE_TEST_LOG}"
raw_profile_buffer_size=$(grep length "${COVERAGE_TEST_LOG}" | sed "s/.*length: \([0-9]*\) bytes.*/\1/" || echo "UNKNOWN")
log "Raw profile buffer is ${raw_profile_buffer_size} bytes"
# Process raw profile data
util/coverage/device_profile_data.py --input_file "${COVERAGE_TEST_LOG}" prof.raw
# Check the contents
/tools/riscv/bin/llvm-cov --version
/tools/riscv/bin/llvm-profdata show prof.raw || true
