#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

INPUT_DIR="${1:-/tmp/$USER/coverage_report}"
OUTPUT_DIR="${2:-/tmp/$USER/merged_coverage}"

INPUT_DIR="$(realpath "${INPUT_DIR}")"
OUTPUT_DIR="$(realpath "${OUTPUT_DIR}")"
TESTS="${OUTPUT_DIR}/test_coverages"
SOURCES="${OUTPUT_DIR}/source_files"
COVERAGE="${OUTPUT_DIR}/coverage.dat"
HTML_REPORT="${OUTPUT_DIR}/html_report"

echo "Merge artifacts from all jobs"
function merge_dir() {
  local dir="$1"
  mkdir -p "${OUTPUT_DIR}/${dir}"
  find "${INPUT_DIR}" -type d -name "${dir}" \
    -exec echo "Merging {} to ${dir}" \; \
    -exec rsync -a {}/ "${OUTPUT_DIR}/${dir}/" \;
}
merge_dir "test_coverages"
merge_dir "source_files"
merge_dir "test_logs"

echo "Merge all coverage data"
find "${TESTS}" -type f -name "*.dat" -exec cat {} + > "${COVERAGE}"

echo "Merge static inline copies"
# i.e. Replace all `FN:lineno,xxx:name` to FN:lineno,name
sed -i -E 's/^FN:([0-9]+),.+:([^:]+)$/FN:\1,\2/' "${COVERAGE}"
sed -i -E 's/^FNDA:([0-9]+),.+:([^:]+)$/FNDA:\1,\2/' "${COVERAGE}"

echo "Merge all generated files"
if [[ -d "${SOURCES}/bazel-out" ]]; then
  mkdir -p "${SOURCES}/generated/"
  find "${SOURCES}/bazel-out" -maxdepth 1 -type d -name "k8-*" \
    -exec echo "Merging {} to generated/" \; \
    -exec rsync -a {}/ "${SOURCES}/generated/" \;
  sed -i 's|bazel-out/k8-[^/]*/|generated/|g' "${COVERAGE}"
fi

echo "Render HTML coverage report"
genhtml --version

# LCOV 2 has more data consistency checks that need to be disabled.
IGNORE_ERRORS=()
if ! genhtml --version | grep -q 'LCOV version 1'; then
  IGNORE_ERRORS+=(
    --keep-going
  )
fi

GENHTML_ARGS=(
  --output-directory "${HTML_REPORT}"
  --prefix "${SOURCES}"
)

(
  cd "${SOURCES}"
  genhtml "${COVERAGE}" "${IGNORE_ERRORS[@]}" "${GENHTML_ARGS[@]}"
  lcov "${IGNORE_ERRORS[@]}" --summary "${COVERAGE}" > "${GITHUB_STEP_SUMMARY:-/dev/null}"
)

echo "Pack directories to reduce artifact size and count"
function pack_dir() {
  local dir="$1"
  echo "Packing ${dir}.tar.gz"
  tar -czf "${OUTPUT_DIR}/${dir}.tar.gz" -C "${OUTPUT_DIR}" "${dir}"
  rm -rf "${OUTPUT_DIR:?}/${dir:?}"
}
pack_dir "test_coverages"
pack_dir "source_files"
pack_dir "test_logs"
