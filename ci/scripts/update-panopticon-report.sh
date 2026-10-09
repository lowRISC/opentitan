#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

REPO_ROOT="$(pwd)"
INPUT_DIR="$(realpath "${1:-bazel-testlogs}")"
OUTPUT_DIR="$(realpath -m "${2:-/tmp/${USER:-ci}/panopticon_report}")"
STATE_FILE="$(realpath -m "${3:-${OUTPUT_DIR}/panopticon_state.json.gz}")"
COMMIT_SHA="${GITHUB_SHA:-$(git rev-parse HEAD 2>/dev/null || echo "")}"

mkdir -p "${OUTPUT_DIR}/viewer"

echo "Aggregating OTBN Panopticon FI and TVLA artifacts from ${INPUT_DIR}"
./bazelisk.sh run //hw/ip/otbn/util/panopticon:aggregate -- \
  --state-file="${STATE_FILE}" \
  --input-dir="${INPUT_DIR}" \
  --repo-root="${REPO_ROOT}" \
  --commit="${COMMIT_SHA}" \
  --output-html="${OUTPUT_DIR}/viewer/index.html"
