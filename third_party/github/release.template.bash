#!/usr/bin/env bash

# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

ARTIFACTS=(@@ARTIFACTS@@)
FILES=(@@FILES@@)
GH=@@GH@@
REMOTE="@@REMOTE@@"
@@ENV@@

BRANCH=$(cd "$BUILD_WORKSPACE_DIRECTORY" && git branch --show-current)
RELEASE_TAG=$(cd "$BUILD_WORKSPACE_DIRECTORY" && git describe --abbrev=0 --tags)

if $(${GH} release list | egrep -q "\s${RELEASE_TAG}\s"); then
    echo "A release with tag ${RELEASE_TAG} already exists."
    echo
    echo "To make a new release, create a new tag first."
    exit 1
fi

declare -A DIGEST=()
for f in "${FILES[@]}"; do
    b=$(basename ${f})
    DIGEST[${b}]=$(sha256sum ${f} | cut -f1 -d' ')
done

export ARTIFACTS BRANCH FILES GH REMOTE RELEASE_TAG DIGEST
@@SCRIPT@@

${GH} release create --target="${BRANCH}" "$@" "${RELEASE_TAG}" "${ARTIFACTS[@]}"
