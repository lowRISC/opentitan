#!/bin/bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# WARNING This is a template where some x strings will be expanded by
# the rules in qemu.bzl.
set -e

qemu=__qemu__
qemu_args=( __qemu_args__  )
test_harness="__test_harness__"
otp="__otp__"
flash="__flash__"
test_cmd=( __test_cmd__ )
args=( __args__ )

mutable_flash="flash_img.bin"
mutable_otp="otp_img.raw"

test_args=( "$@" )
qemu_test_args=()
harness_test_args=()
# Intercept all test args of the form --qemu-arg=X
# and pass X to qemu directly.
# For convenience, a variant with "--qemu-args=X Y Z" is also
# supported when all space-separated substrings of the arguments
# will be expanded to different QEMU arguments.
# Everything else will be passed as-in to the test harness.
for this_arg in "${test_args[@]}"; do
    if [[ $this_arg == --qemu-arg=* ]]; then
        qemu_test_args+=( "${this_arg#--qemu-arg=}" )
    elif [[ $this_arg == --qemu-args=* ]]; then
        # See https://stackoverflow.com/a/45201229
        # and https://unix.stackexchange.com/a/519917
        readarray -t -d ' ' a < <(printf '%s' "${this_arg#--qemu-args=}")
        qemu_test_args+=( "${a[@]}" )
    else
        harness_test_args+=( "$this_arg" )
    fi
done

cleanup() {
    rm -f "${mutable_otp}" "${mutable_flash}"
    rm -f qemu-monitor qemu.log
}
trap cleanup EXIT

# QEMU requires mutable flash and OTP files but Bazel only provides RO
# files so we have to create copies unique to this test run.
cp "${otp}" "${mutable_otp}" && chmod +w "${mutable_otp}"
if [ -n "${flash}" ]; then
    cp "${flash}" "${mutable_flash}" && chmod +w "${mutable_flash}"
fi

# QEMU disconnects from `stdout` when it daemonizes so we need to stream
# the log through a pipe:
mkfifo qemu.log && cat qemu.log &

echo "Starting QEMU: ${qemu} ${qemu_test_args[*]} ${qemu_args[*]}"
"${qemu}" "${qemu_test_args[@]}" "${qemu_args[@]}"

echo "Invoking test: ${test_harness} ${args[*]} ${harness_test_args[*]} ${test_cmd[*]}"
"${test_harness}" "${args[@]}" "${harness_test_args[@]}" "${test_cmd[@]}"
