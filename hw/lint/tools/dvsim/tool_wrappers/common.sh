#!/usr/bin/env bash
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This function uses Bazel to run the named Verible tool.
#
# @param VERIBLE_TOOL The name of the tool to run, e.g. "verible-verilog-lint".
# @param ARGS,...  Arguments that are forwarded to the Verible tool.
verible_wrapper_run () {
    set -e
    VERIBLE_TOOL="$1"
    shift

    [ -v DVSIM_PROJ_ROOT ]
    [ -v DVSIM_SCRATCH_PATH ]

    # Dvsim invokes fusesoc on various IP blocks in parallel, and fusesoc runs
    # the Verible tools, e.g. verible-verilog-lint. As a result, multiple
    # instances of this function may be running simultaneously.
    #
    # We need to use Bazel to get the binary for the desired Verible tool, but
    # simply offloading to `bazel run` would create a performance bottleneck;
    # each parallel Bazel invocation will wait for the others to complete.
    #
    # Instead, this script does its own lock management to guarantee that the
    # Verible tool's binary is present before executing it. Critically, it
    # releases the lock *before* running the tool.
    LOCKFILE="$DVSIM_SCRATCH_PATH/../dvsim-tool-wrapper.lock"

    BAZEL_EXECROOT_CACHE_FILE="$DVSIM_SCRATCH_PATH/../bazel_execroot_cache.txt"
    if [ ! -e "$BAZEL_EXECROOT_CACHE_FILE" ]; then
        (
            # Acquire an exclusive lock on the file descriptor.
            flock --exclusive 9

            # Run the tool with Bazel to ensure the binary is present.
            #
            # Bazel prints an unhelpful warning to stderr when running an
            # external binary that it considers to be a source file. Silencing
            # this warning prevents the veriblelint report parser from taking it
            # seriously.
            SPURIOUS_WARNING_PATTERN="is a source file, nothing will be built for it. If you want to build a target that consumes this file, try --compile_one_dependency"
            "$DVSIM_PROJ_ROOT/bazelisk.sh" run "@verible//:bin/$VERIBLE_TOOL" \
                -- --version 2> >(grep -v "$SPURIOUS_WARNING_PATTERN")

            # Cache Bazel's execution root so we can find the binary without
            # running Bazel next time.
            "$DVSIM_PROJ_ROOT/bazelisk.sh" info execution_root > "$BAZEL_EXECROOT_CACHE_FILE"
        ) 9>"$LOCKFILE"
    fi

    BAZEL_EXECROOT="$(cat "$BAZEL_EXECROOT_CACHE_FILE")"
    "$BAZEL_EXECROOT/external/verible/bin/$VERIBLE_TOOL" "$@"
}
