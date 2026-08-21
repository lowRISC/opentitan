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
#     nix run .#lint -- hygiene format
#
# This wrapper maps the old "quick lint" set onto the new categories and
# assumes the required tools are already on PATH.

set -e

tgt_branch="${1:-master}"

repo_top="$(git rev-parse --show-toplevel)"
OT_BASE_REF="$tgt_branch" exec "$repo_top/ci/lint/run.sh" hygiene format
