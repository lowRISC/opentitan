#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This script wraps 'pkg-config' to work around Bazel sandbox path changes.
#
# Cargo build scripts (via the 'pkg-config' Rust crate) call 'pkg-config' to find
# library paths. In Bazel, these paths reside under configuration-dependent
# 'bazel-out/' directories (e.g., 'bazel-out/k8-fastbuild/...'), which cannot be
# hardcoded in MODULE.bazel.
#
# To solve this:
# 1. We pass the path to a *single* generated .pc file using Bazel's '$(location)'
#    expansion in 'build_script_env' (saved in PKG_CONFIG_PATH_FILE).
# 2. This wrapper script intercepts the call, extracts the directory containing
#    that file, and exports it as 'PKG_CONFIG_PATH'.
# 3. It then forwards the call to the real 'pkg-config'.
#
# This ensures 'pkg-config' always finds the correct .pc files regardless of the
# Bazel build configuration or sandbox relocation.

if [ -n "$PKG_CONFIG_PATH_FILE" ]; then
    # Extract the directory containing the .pc file.
    PKG_CONFIG_PATH=$(dirname "$PKG_CONFIG_PATH_FILE")
    export PKG_CONFIG_PATH
    # Unset to avoid leaking Bazel-specific env var to the child process.
    unset PKG_CONFIG_PATH_FILE
fi

# Forward the call to the system pkg-config.
exec pkg-config "$@"
