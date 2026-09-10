#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Deprecated compatibility shim.
#
# The lint flow now lives in ci/lint/run.sh, which is the single source of
# truth shared by CI and local runs. Prefer running it (with all tools
# provided) via:
#
#     nix run .#lint -- gen hw bazel
#
# This wrapper maps the old "slow lint" set onto the new categories and
# assumes the required tools (including Bazel) are already on PATH.

set -e

repo_top="$(git rev-parse --show-toplevel)"
exec "$repo_top/ci/lint/run.sh" gen hw bazel
