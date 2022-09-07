#!/bin/bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a wrapper script for `bazelisk` that downloads and executes bazelisk.
# Bazelisk is a wrapper for `bazel` that can download and execute the project's
# required bazel version.
#
# CI jobs should use ci/bazelisk.sh instead, which performs CI-friendly additional
# setup.

set -euo pipefail

# Change to this script's directory, as it is the location of the bazel workspace.
cd "$(dirname "$0")"

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
    local arch
    arch="$(uname -m -o)"
    echo "${architectures[$arch]:-${arch}}"
}

function check_hash() {
    local file target
    file="$1"
    target="$(os_arch)"
    echo "${hashes[$target]}  $file" | sha256sum --check --quiet
}

function prepare() {
    local target
    target="$(os_arch)"
    local bindir="${REPO_TOP}/${BINDIR}"
    local file="${bindir}/bazelisk"
    local url="https://github.com/bazelbuild/bazelisk/releases/download/${release}/bazelisk-${target}"

    mkdir -p "$bindir"
    echo "Downloading bazelisk ${release} (${url})." >> $bindir/bazelisk.log
    curl ${CURL_FLAGS} --location "$url" --output "$file"
    chmod +x "$file"
}

function up_to_date() {
    local file="$1"
    # We need an update if the file doesn't exist or it has the wrong hash
    test -f "$file" || return 1
    check_hash "$file" || return 1
    return 0
}

function outquery_starlark_expr() {
    local query="$1"
    shift
    if [[ ${query} == "outquery" ]]; then
        q="-one"
    else
        q=${query#outquery}
    fi

    case "$q" in
        -one)
            echo "target.files.to_list()[0].path"
            ;;
        -all)
            echo "\"\\n\".join([f.path for f in target.files.to_list()])"
            ;;
        -*)
            echo "\"\\n\".join([f.path for f in target.files.to_list() if \"$q\"[1:] in f.path])"
            ;;
        .*)
            echo "\"\\n\".join([f.path for f in target.files.to_list() if f.path.endswith(\"$q\")])"
            ;;
    esac
}

function main() {
    local bindir="${REPO_TOP}/${BINDIR}"
    local file="${bindir}/bazelisk"
    local lockfile="${bindir}/bazelisk.lock"

    if ! up_to_date "$file"; then
        # Grab the lock, blocking until success. Upon success, check again
        # whether we're up to date (because some other process might have
        # downloaded bazelisk in the meantime). If not, download it ourselves.
        mkdir -p "$bindir"
        (flock -x 9; up_to_date "$file" || prepare) 9>>"$lockfile"
    fi
    if ! check_hash "$file"; then
        echo "sha256sum doesn't match expected value"
        exit 1
    fi

    case "$1" in
        outquery*)
            # The custom 'outquery' command can be used to query bazel for the
            # outputs associated with labels.
            # The outquery command can take several forms:
            #   outquery: return one output file associated with the label.
            #   outquery-all: return all output files associated with the label.
            #   outquery-x: return output files containing the substring "x".
            #   outquery.x: return output files ending with the substring ".x".
            QEXPR="$(outquery_starlark_expr "$1")"
            shift
            exec "$file" cquery "$@" \
                --output=starlark --starlark:expr="$QEXPR" \
                --ui_event_filters=-info --noshow_progress
            ;;
        *)
            exec "$file" "$@"
            ;;
    esac
}

main "$@"
