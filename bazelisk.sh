#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a wrapper script for `bazelisk` that downloads and executes bazelisk.
# Bazelisk is a wrapper for `bazel` that can download and execute the project's
# required bazel version.

set -euo pipefail

: "${CURL_FLAGS:=--silent}"
: "${REPO_TOP:=$(git rev-parse --show-toplevel)}"
: "${BINDIR:=.bin}"

readonly release="v1.11.0"
declare -A hashes=(
    # sha256sums for v1.11.0.  Update this if you update the release.
    [linux-amd64]="231ec5ca8115e94c75a1f4fbada1a062b48822ca04f21f26e4cb1cd8973cd458"
)

declare -A architectures=(
    # Map `uname -m -o` to bazelisk's precompiled binary target names.
    [x86_64 GNU/Linux]="linux-amd64"
)

function os_arch() {
    local arch="$(uname -m -o)"
    echo "${architectures[$arch]:-${arch}}"
}

function check_hash() {
    local file="$1"
    local target="$(os_arch)"
    local value="$(sha256sum "${file}" | cut -f1 -d' ')"
    local expect="${hashes[$target]}"
    return $(test "$value" == "$expect")
}

function prepare() {
    local target="$(os_arch)"
    local bindir="${REPO_TOP}/${BINDIR}"
    local file="${bindir}/bazelisk"
    local url="https://github.com/bazelbuild/bazelisk/releases/download/${release}/bazelisk-${target}"

    echo "Downloading bazelisk ${release} (${url})."
    mkdir -p "$bindir"
    curl ${CURL_FLAGS} --location "$url" --output "$file"
    chmod +x "$file"
}

function main() {
    local file="${REPO_TOP}/${BINDIR}/bazelisk"
    if [[ ! -f "$file" ]] || ! check_hash "$file"; then
        prepare
    fi
    if ! check_hash "$file"; then
        echo "sha256sum doesn't match expected value"
        exit 1
    fi
    exec "$file" "$@"
}

main "$@"
