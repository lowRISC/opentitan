#!/bin/bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# WARNING This is a template where some x strings will be expanded by
# the rules in qemu.bzl.

set -e

# Retrieve/set various templated values from Bazel
export QEMU_BIN="__qemu_bin__"
export QEMU_CONFIG="__config__"
export QEMU_ROM="__rom__"
export QEMU_OTP="__otp__"
export QEMU_FLASH="__flash__"
export QEMU_ICOUNT="__icount__"

qemu_start="__qemu_start__"
qemu_args=( __qemu_args__  )

test_harness="__test_harness__"
test_cmd=( __test_cmd__ )
args=( __args__ )

test_args=( "$@" )
qemu_test_args=()
harness_test_args=()

# Intercept all test args of the form --qemu-arg=X and pass X to qemu directly.
# For convenience, a variant with "--qemu-args=X Y Z" is also supported when all
# space-separated substrings of the arguments will be expanded to different QEMU
# arguments. Everything else will be passed as-in to the test harness.
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

# For provided OTP and flash files, create mutable copies as Bazel will provide
# read-only files by default
mutable_otp="otp_img.mut.raw"
if [ ! -w "$QEMU_OTP" ]; then
    cp "$QEMU_OTP" "$mutable_otp" && chmod +w "$mutable_otp"
    export QEMU_OTP="$mutable_otp"
fi

mutable_flash="flash_img.mut.bin"
if [ -n "$QEMU_FLASH" ] && [ ! -w "$QEMU_FLASH" ]; then
    cp "$QEMU_FLASH" "$mutable_flash" && chmod +w "$mutable_flash"
    export QEMU_FLASH="$mutable_flash"
fi

# Create backing storage for flash device on SPI Host 0/SPI Device SPI bus
export QEMU_SPIFLASH="spiflash.bin"
dd if=/dev/zero "of=$QEMU_SPIFLASH" bs=1M count=32 status=none
chmod +w "$QEMU_SPIFLASH"

# Define paths to capture QEMU's log, PID and for CharDevs (PTYs / sockets)
export QEMU_LOG="qemu.log"
export QEMU_PIDFILE="qemu.pid"
export QEMU_MONITOR="qemu-monitor"
export QEMU_RV_DM_JTAG_SOCK="qemu-jtag.sock"
export QEMU_LC_JTAG_SOCK="qemu-jtag-lc-ctrl.sock"

qemu_pid=""

# Set trap handler to clean up generated files and QEMU itself on exit
# This allows us to `./bazelisk.sh run` tests repeatedly.
cleanup() {
    ret=$?
    set +e

    if [ -n "$qemu_pid" ] && kill -0 "$qemu_pid" 2>/dev/null; then
        echo "Stopping QEMU: $qemu_pid"
        # If 2 seconds pass and QEMU is still alive, force kill it.
        (
          sleep 2
          if kill -0 "$qemu_pid" 2>/dev/null; then
            echo "Killing QEMU: $qemu_pid"
            kill -KILL "$qemu_pid" 2>/dev/null
          fi
        ) &
        # Ask QEMU to gracefully terminate (SIGTERM) first
        kill "$qemu_pid"
    fi

    # Clean up created log, PID and SPI Flash files
    rm -f "$QEMU_LOG" "$QEMU_PIDFILE" "$QEMU_SPIFLASH"

    # Remove mutable OTP and flash copies
    rm -f "$mutable_otp" "$mutable_flash"

    # Clean up CharDevs
    rm -f "$QEMU_MONITOR" "$QEMU_RV_DM_JTAG_SOCK" "$QEMU_LC_JTAG_SOCK"

    exit "$ret"
}
trap cleanup EXIT

# QEMU disconnects from `stdout` when it daemonizes so we need to stream
# the log through a pipe:
mkfifo "$QEMU_LOG" && cat "$QEMU_LOG" &

# Start QEMU and record the daemon's PID for cleanup. Relevant files/binaries
# are passed via defined environment variables
"$qemu_start" "${qemu_test_args[@]}" "${qemu_args[@]}"
qemu_pid=$(cat "$QEMU_PIDFILE")

# Start the test harness to interact with QEMU
echo "Invoking test: ${test_harness} ${args[*]} ${harness_test_args[*]} ${test_cmd[*]}"
"${test_harness}" "${args[@]}" "${harness_test_args[@]}" "${test_cmd[@]}"
