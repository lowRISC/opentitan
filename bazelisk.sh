#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a wrapper script for `bazelisk` that downloads and executes bazelisk.
# Bazelisk is a wrapper for `bazel` that can download and execute the project's
# required bazel version.

set -eo pipefail

# Change to this script's directory, as it is the location of the bazel workspace.
cd "$(dirname "$0")"

: "${CURL_FLAGS:=--silent}"
: "${REPO_TOP:=$(git rev-parse --show-toplevel)}"
: "${BINDIR:=.bin}"
: "${BAZEL_BIN:=$(which bazel 2>/dev/null)}"

# Bazelisk (not Bazel) release. Keep this in sync with `util/container/Dockerfile`.
readonly release="v1.24.1"
declare -A hashes=(
    # sha256sums for v1.24.1.  Update this if you update the release.
    [linux-amd64]="0aee09c71828b0012750cb9b689ce3575da8e230f265bf8d6dcd454eee6ea842"
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
            echo "\"\\n\".join([f.path for f in depset(transitive=[target.files, target.default_runfiles.files]).to_list()])"
            ;;
        -providers)
            echo "providers(target)"
            ;;
        -*)
            echo "\"\\n\".join([f.path for f in depset(transitive=[target.files, target.default_runfiles.files]).to_list() if \"$q\"[1:] in f.path])"
            ;;
        .*)
            echo "\"\\n\".join([f.path for f in depset(transitive=[target.files, target.default_runfiles.files]).to_list() if f.path.endswith(\"$q\")])"
            ;;
    esac
}

# Arguments:
# $qexpr: starlark expression - see `outquery_starlark_expr`
# $name: name of an array containing Bazel arguments that should come _before_
#        the subcommand (e.g. `--bazelrc=...`).
function do_outquery() {
    local qexpr="$1"
    shift

    "$file" "${pre_cmd_args[@]}" cquery "$@" \
        --output=starlark --starlark:expr="$qexpr" \
        --ui_event_filters=-info --noshow_progress \
        | sort | uniq
}

function main() {
    local bindir="${REPO_TOP}/${BINDIR}"
    local file="${BAZEL_BIN:-${bindir}/bazelisk}"
    local lockfile="${bindir}/bazelisk.lock"

    # If the user has Bazel in their PATH, check its version.
    # Fallback to bazelisk if it doesn't match.
    if [ -x "$BAZEL_BIN" ]; then
        if [ "$("$BAZEL_BIN" --version)" != "bazel $(cat .bazelversion)" ]; then
            file="${bindir}/bazelisk"
        fi
    fi

    # Are we using bazel from the user's PATH or using bazelisk?
    if expr match "${file}" ".*bazelisk$" >/dev/null; then
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
    fi

    # Shift all flags (starting with `-`) that come before the subcommand
    # into an array.
    pre_cmd_args=()
    while [[ "${1-}" == -* ]]; do
        pre_cmd_args+=("$1")
        shift
    done

    case "${1-}" in
        outquery*)
            # The custom 'outquery' command can be used to query bazel for the
            # outputs associated with labels.
            # The outquery command can take several forms:
            #   outquery: return one output file associated with the label.
            #   outquery-all: return all output files associated with the label.
            #   outquery-x: return output files containing the substring "x".
            #   outquery.x: return output files ending with the substring ".x".
            local qexpr
            qexpr="$(outquery_starlark_expr "$1")"
            shift
            do_outquery "$qexpr" "$@"
            ;;
        build-then)
            # The 'build-then' command builds the requested targets and then
            # evaluates the given command template, replacing "%s" with the path
            # to an output file.
            #
            # For example, the command below would build "//:foo" and run "less"
            # on one of the output files.
            #
            #     ./bazelisk.sh build-then "less %s" //:foo
            shift
            local command_template="$1"
            shift
            local qexpr outfile
            qexpr="$(outquery_starlark_expr outquery)"
            outfile=$(do_outquery "$qexpr" "$@")
            "$file" "${pre_cmd_args[@]}" build "$@"
            # shellcheck disable=SC2059
            # We are intentionally using $command_template as a format string.
            eval "$(printf "$command_template" "$outfile")"
            ;;
        sync)
            # The `sync` command has been disabled when using Bzlmod in favour of
            # `fetch`. For some reason Bazel crashes when you try to use `sync`
            # rather than printing a helpful error message.
            #
            # When run interactively, print a deprecation error and exit.
            # When run in a script, intercept `sync` commands and forward them
            # to `fetch` which is more or less identical. This ensures Git hooks
            # will continue working on this branch and older branches which do
            # not support `bazel fetch --configure` yet.
            if [ -t 0 ]; then
                echo 'ERROR: The `bazel sync` command has been deprecated.' >&2
                echo '       Use `bazel fetch` instead.'                    >&2
                exit 1
            else
                shift
                exec "$file" "${pre_cmd_args[@]}" fetch "$@"
            fi
            ;;
        *)
            exec "$file" "${pre_cmd_args[@]}" "$@"
            ;;
    esac
}

main "$@"
