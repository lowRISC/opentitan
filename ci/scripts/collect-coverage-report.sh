#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

OUTPUT_DIR="${1:-/tmp/$USER/coverage_report}"
TESTS="${OUTPUT_DIR}/test_coverages"
LOGS="${OUTPUT_DIR}/test_logs"
SOURCES="${OUTPUT_DIR}/source_files"
COVERAGE="${OUTPUT_DIR}/coverage.dat"

LCOV_FILES="bazel-out/_coverage/lcov_files.tmp"

if [[ ! -f "${LCOV_FILES}" ]]; then
  echo "[!] Coverage metadata ${LCOV_FILES} not found. Skipping coverage report."
  echo "coverageReport=missing" >> "${GITHUB_OUTPUT:-/dev/null}"
  exit 0
fi

echo "Collect coverage metadata"
mkdir -p "${OUTPUT_DIR}"
cp -r bazel-out/_coverage/* "${OUTPUT_DIR}" || true
find "${OUTPUT_DIR}" -type f -exec chmod 644 {} +

echo "Collect all test coverage data"
mkdir -p "${TESTS}"
rsync -a --ignore-missing-args --files-from="${LCOV_FILES}" . "${TESTS}/"

echo "Merge all coverage data"
find "${TESTS}" -type f -name "*.dat" -exec cat {} + > "${COVERAGE}"

echo "Collect all test logs"
mkdir -p "${LOGS}"
cat "${LCOV_FILES}" | while read -r lcov; do
  test_dir=$(dirname "${lcov}")
  if [[ -f "${test_dir}/test.xml" ]]; then
    mkdir -p "${LOGS}/${test_dir}"
    cp "${test_dir}/test.xml" "${LOGS}/${test_dir}/"
    echo "Copied ${test_dir}/test.xml"
  fi
done

echo "Collect all source files listed in coverage data"
mkdir -p "${SOURCES}"
grep -h '^SF:' "${COVERAGE}" | sed 's/^SF://' | sort -u \
| rsync -a --ignore-missing-args --files-from=- . "${SOURCES}/"

echo "coverageReport=ok" >> "${GITHUB_OUTPUT:-/dev/null}"
