#!/bin/bash
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

set -x
set -e

. util/build_consts.sh

if [ $# == 0 ]; then
    echo >&2 "Usage: run-fpga-tests.sh <fpga> <target_pattern_file> [bazel options...]"
    echo >&2 "E.g. ./run-fpga-tests.sh cw340 list_of_test.txt --cache_test_results=no"
    exit 1
fi
fpga="$1"
target_pattern_file="$2"
shift 2

# Copy bitstreams and related files into the cache directory so Bazel will have
# the corresponding targets in the @bitstreams workspace.
readonly BIT_CACHE_DIR="${HOME}/.cache/opentitan-bitstreams/cache/ci_bitstreams"
readonly BIT_SRC_DIR="${BIN_DIR}/hw/top_earlgrey/chip_earlgrey_${fpga}"
mkdir -p "${BIT_CACHE_DIR}"
cp -rt "${BIT_CACHE_DIR}" "${BIT_SRC_DIR}"/*

export BITSTREAM="--offline --list ci_bitstreams"

# TEMPORARY DEBUG: investigating intermittent "Found no USB device" failures.
# Snapshots USB state before the first USB access.
echo "DEBUG: container cgroup: $(cat /proc/self/cgroup 2>/dev/null | head -1)"
echo "DEBUG: running as: $(id)"
echo "DEBUG: environment (looking for whatever tells us which board this container was assigned):"
env | sort | sed 's/^/DEBUG:   /'
echo "DEBUG: /proc/1/environ of PID 1 in this container (in case the assignment is only visible to the entrypoint):"
(cat /proc/1/environ 2>/dev/null | tr '\0' '\n' | sort | sed 's/^/DEBUG:   /') || echo "DEBUG:   could not read /proc/1/environ"

dump_cw340_state() {
    local label="$1"
    local ts cw_lines cw_accessible dev name vid pid bus devn node status line cw_verdict
    ts="$(date -u '+%Y-%m-%dT%H:%M:%S.%3NZ' 2>/dev/null || date -u)"
    cw_lines=()
    cw_accessible=0
    for dev in /sys/bus/usb/devices/*/; do
        name="$(basename "$dev")"
        case "$name" in *:*) continue ;; esac
        [ -f "${dev}idVendor" ] || continue
        vid="$(cat "${dev}idVendor" 2>/dev/null)"
        [ "$vid" = "2b3e" ] || continue
        pid="$(cat "${dev}idProduct" 2>/dev/null || echo '?')"
        bus="$(cat "${dev}busnum" 2>/dev/null || echo '?')"
        devn="$(cat "${dev}devnum" 2>/dev/null || echo '?')"
        node="$(printf '/dev/bus/usb/%03d/%03d' "$bus" "$devn" 2>/dev/null)"
        if [ -c "$node" ]; then
            status="accessible"
            cw_accessible=$((cw_accessible + 1))
        else
            status="MISSING"
        fi
        cw_lines+=("$name pid=$pid busnum=$bus devnum=$devn -> $node $status")
    done

    if [ "$cw_accessible" = 1 ]; then
        cw_verdict="HEALTHY"
    elif [ "$cw_accessible" = 0 ]; then
        cw_verdict="PROBLEM - this container's own board is not reachable"
    else
        cw_verdict="PROBLEM - more than one board accessible, expected exactly one"
    fi
    echo "DEBUG: ===== CW340 SUMMARY [$label @ $ts]: found=${#cw_lines[@]} accessible=$cw_accessible -> $cw_verdict ====="
    for line in "${cw_lines[@]}"; do
        echo "DEBUG:   $line"
    done
}

dump_cw340_state "before first USB access"

# We will lose serial access when we reboot, but if tests fail we should reboot
# in case we've crashed the UART handler on the CW340's SAM3U
# Note that the hyperdebug backend does not have the reset-sam3x command so this will fail but not trigger an error.
cleanup() {
    ./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="${fpga}" fpga reset-sam3x || true
    dump_cw340_state "immediately after reset-sam3x"
    sleep 5
    dump_cw340_state "5s after reset-sam3x (settled)"
}
trap cleanup EXIT

# Running tests will clear all non-volatile memory on the FPGA, but we start by
# clearing the bitstream to be cautious in case tests leave behind some state.
# FIXME: #16543 The following step sometimes has trouble reading the I2C we'll
# log it better and continue even if it fails (the pll is mostly correctly set
# anyway).
# Note that the hyperdebug backend does not have the set-pll command so this will fail but not trigger an error.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" --logging debug fpga set-pll || true
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga clear-bitstream

# Print the SAM3X firmware version. HyperDebug transports don't currently support this, so we ignore errors.
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface="$fpga" fpga get-sam3x-fw-version || true

./bazelisk.sh test \
    --run_under=//ci/scripts:run_test \
    --define DISABLE_VERILATOR_BUILD=true \
    --nokeep_going \
    --test_output=all \
    --build_tests_only \
    --define "$fpga"=lowrisc \
    --flaky_test_attempts=2 \
    --target_pattern_file="${target_pattern_file}" "$@"
