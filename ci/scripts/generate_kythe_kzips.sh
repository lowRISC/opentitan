#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
set -e

print_usage () {
    cat <<EOF
Usage: $0 MERGED_KZIP_PATH

This script builds Bazel targets with a special Kythe-infused configuration that
causes it to generate many "kzip" files along the way. After building, the
script merges the intermediate kzips and writes the result to MERGED_KZIP_PATH.
This final kzip is suitable for ingestion by Google's OSS codesearch [0].

By default, the script assumes it's running in GitHub Actions. However, if it
sees the OT_OUTSIDE_GITHUB_ACTIONS environment variable, it will happily
simulate the necessary parts of the GitHub Actions environment. For example:

    OT_OUTSIDE_GITHUB_ACTIONS=1 $0 merged.kzip

[0]: https://cs.opensource.google/opentitan
EOF
}

MERGED_KZIP_PATH=$1

if [[ -n "${OT_OUTSIDE_GITHUB_ACTIONS}" ]]; then
    # Simulate the GitHub Action environment when debugging locally.
    GITHUB_WORKSPACE="$(pwd)"
    RUNNER_TEMP="/tmp/kythe-kzips"
    mkdir -p "${RUNNER_TEMP}"
fi

assert_var_nonempty () {
    VAR_NAME="$1"
    if [[ -z "${!VAR_NAME}" ]] ; then
       echo "Assertion failed: ${VAR_NAME} must be non-empty."
       echo
       print_usage
       exit 1
    fi
}

# Assert that script arguments are defined and non-empty.
assert_var_nonempty MERGED_KZIP_PATH
# Assert that GitHub Action environment variable are defined and non-empty.
assert_var_nonempty GITHUB_WORKSPACE
assert_var_nonempty RUNNER_TEMP

# Release tag from https://github.com/kythe/kythe/releases/
KYTHE_VERSION="v0.0.60"
KYTHE_DIR="${RUNNER_TEMP}/kythe-${KYTHE_VERSION}"
KYTHE_SHA256="8fe1aeb8f514306f26e233077e1156dbe353ef2afa72c37866bebb680b52a10d"
KYTHE_TAR_GZ="kythe.tar.gz"

set -euxo pipefail

mkdir -p "${KYTHE_DIR}"

cd "${RUNNER_TEMP}"

if [[ ! -e "${KYTHE_TAR_GZ}" ]]; then
  wget --quiet -O "${KYTHE_TAR_GZ}" \
    "https://github.com/kythe/kythe/releases/download/${KYTHE_VERSION}/kythe-${KYTHE_VERSION}.tar.gz"
  echo "${KYTHE_SHA256}  ${KYTHE_TAR_GZ}" | sha256sum --check --quiet
  mkdir -p "${KYTHE_DIR}"
  tar --strip-components=1 --no-same-owner -xvzf "${KYTHE_TAR_GZ}" \
    --directory "${KYTHE_DIR}"
fi

# TODO(lowRISC/opentitan#13935) Enable Rust extraction.
#
# Disable Rust extraction by deleting an action listener line from Kythe's
# extractors.bazelrc[1]. The problem is that Kythe's bazel_rust_extractor
# (v0.0.60) has a hardcoded dependency on librustc_driver-3ff8a78cc1a3c248.so,
# which is not included in the release.
#
# [1]:
#   https://cs.opensource.google/kythe/kythe/+/master:kythe/extractors/bazel/extractors.bazelrc
#   (Note that this link points to the repo's HEAD, not a particular release.)
sed -Ei \
  's%^build --experimental_action_listener=@kythe_release//:extract_kzip_rust$%%' \
  "${KYTHE_DIR}/extractors.bazelrc"

cd "${GITHUB_WORKSPACE}"

./bazelisk.sh \
  --bazelrc="${KYTHE_DIR}/extractors.bazelrc" \
  build \
  --build_tag_filters="-cw310,-verilator" \
  --define DISABLE_VERILATOR_BUILD=true \
  --define bitstream=skip \
  --override_repository kythe_release="${KYTHE_DIR}" \
  --define=kythe_corpus=github.com/lowRISC/opentitan \
  -- //sw/... -//third_party/...

find ./bazel-out/*/extra_actions -name '*.kzip' -print0 \
  | xargs --null "${KYTHE_DIR}/tools/kzip" merge -output "${MERGED_KZIP_PATH}"
