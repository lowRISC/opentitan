#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script currently assumes it is used for chip_earlgrey_cw310.

set -ex

. util/build_consts.sh

readonly TOPLEVEL=top_earlgrey
readonly TOPLEVEL_BIN_DIR="${BIN_DIR}/hw/${TOPLEVEL}/chip_earlgrey_cw310"
readonly TARGET="//hw/bitstream:chip_earlgrey_cw310_cached_fragment"
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
  ${MANIFEST_DIR}/ $BIN_DIR/hw/top_earlgrey/chip_earlgrey_cw310
rm files.txt
