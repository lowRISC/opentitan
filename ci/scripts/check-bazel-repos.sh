#!/bin/bash

# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -e

GIT_REPOS=$(./bazelisk.sh query "kind(new_git_repository, //external:*) union kind(git_repository, //external:*)")
if [[ ${GIT_REPOS} ]]; then
  echo "Bazel's 'git_repository' rule is insecure and incompatible with OpenTitan's airgapping strategy"
  echo "Please replace $GIT_REPOS with an http_archive or new_http_archive"
  exit 1
fi
