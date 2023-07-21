#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script currently assumes it is used for chip_earlgrey_cw310 or
# chip_darjeeling_cw310.

set -ex

if test "$#" -ne 1; then
  echo "Usage: $0 <top name>" >&2
  echo "Example: $0 earlgrey" >&2
  exit 1
fi
readonly TOP_NAME="$1"

. util/build_consts.sh

readonly TOPLEVEL_BIN_DIR="${BIN_DIR}/hw/top_${TOP_NAME}/chip_${TOP_NAME}_cw310"
readonly TARGET="//hw/top_${TOP_NAME}/bitstream:chip_${TOP_NAME}_cw310_cached_fragment"
readonly BAZEL_OPTS=(
  "--define"
  "bitstream=gcp_splice"
)

BITSTREAM=HEAD ci/bazelisk.sh build "${BAZEL_OPTS[@]}" "${TARGET}"
mkdir -p "${TOPLEVEL_BIN_DIR}"
MANIFEST_DIR=$($REPO_TOP/bazelisk.sh cquery --output=starlark \
  --starlark:file=ci/scripts/get-bitstream-fragment-dir.bzl \
  ${TARGET})
echo "$($REPO_TOP/bazelisk.sh cquery --output=starlark \
  --starlark:file=ci/scripts/get-bitstream-fragment-files-relative.bzl \
  ${TARGET})" > files.txt
rsync --archive --copy-unsafe-links --verbose --files-from=files.txt \
  ${MANIFEST_DIR}/ $BIN_DIR/hw/top_${TOP_NAME}/chip_${TOP_NAME}_cw310
rm files.txt
