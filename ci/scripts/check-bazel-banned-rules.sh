#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

GIT_REPOS=$(./bazelisk.sh query "kind('(new_)?git_repository', //external:*)")
if [[ ${GIT_REPOS} ]]; then
  echo "Bazel's 'git_repository' rule is insecure and incompatible with OpenTitan's airgapping strategy."
  echo "Please replace $GIT_REPOS with our 'http_archive_or_local' rule and set a sha256 so it can be canonically reproducible."
  exit 1
fi
