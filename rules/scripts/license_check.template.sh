#!/usr/bin/env bash
#
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

LICENSE_CHECK=@@LICENSE_CHECK@@
ARGS=@@ARGS@@

license_check=$(readlink "$LICENSE_CHECK")

if ! cd "$BUILD_WORKSPACE_DIRECTORY"; then
    echo "Unable to change to workspace (BUILD_WORKSPACE_DIRECTORY: ${BUILD_WORKSPACE_DIRECTORY})"
    exit 1
fi

"$license_check" "${ARGS[@]}"
