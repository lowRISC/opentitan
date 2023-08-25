#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

source util/sh/lib/banners.sh
source util/sh/lib/strict.sh

: "${REPO_TOP:=$(git rev-parse --show-toplevel)}"
PYTHON_REQS_IN_FILE="$REPO_TOP/python-requirements.in"
PYTHON_REQS_OUT_FILE="$REPO_TOP/python-requirements.txt"

# The below shellcode autogenerates the `python-requirements.txt`, with hashes,
# and prepends the license and auto-generated banners at the top of the file.
pip-compile \
  --allow-unsafe \
  --generate-hashes \
  --no-annotate \
  --no-header \
  "$PYTHON_REQS_IN_FILE"
echo -e "\n$(cat "$PYTHON_REQS_OUT_FILE")" > "$PYTHON_REQS_OUT_FILE"
add_autogen_banner "$PYTHON_REQS_OUT_FILE" \
  "./util/sh/scripts/gen-python-requirements.sh"
echo -e "#\n$(cat "$PYTHON_REQS_OUT_FILE")" > "$PYTHON_REQS_OUT_FILE"
add_license_banner "$PYTHON_REQS_OUT_FILE"
