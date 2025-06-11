#!/bin/bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

REPO_TOP="$(git rev-parse --show-toplevel)"
cd "$REPO_TOP"

if grep -r --include '*MODULE.bazel' git_override; then
  echo "Bazel's 'git_override' method is incompatible with OpenTitan's airgapping strategy." >&2
  echo "Please replace all instances with 'archive_override' method and set an 'integrity' so it can be canonically reproducible." >&2
  exit 1
fi
