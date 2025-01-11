#!/bin/bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

REPO_TOP="$(git rev-parse --show-toplevel)"
cd "$REPO_TOP"

if grep -r --include '*.bzl' git_repository; then
  echo "Bazel's 'git_repository' rule is insecure and incompatible with OpenTitan's airgapping strategy."
  echo "Please replace $GIT_REPOS with 'http_archive' rule and set a sha256 so it can be canonically reproducible."
  exit 1
fi
