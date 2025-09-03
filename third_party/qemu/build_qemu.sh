#!/usr/bin/env bash
#
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
set -e

if [ "$#" -ne 2 ]; then
    echo "usage: build_qemu.sh <path to QEMU source> <output archive path>"
    exit 1
fi

QEMU_ROOT="$1"
OUT_ARCHIVE="$(realpath $2)"

# Go to the QEMU source directory.
cd "$QEMU_ROOT"
# Create the build directory if needed.
mkdir -p build
cd build
# Run configure if necessary.
if [ -f config-host.mak ];
then
    echo "Skipping configure, delete $PWD/config-host.mak to reconfigure"
else
    config_log="$PWD/qemu_config.log"
    echo "Configuring QEMU (output log in $config_log)..."
    if ! "$QEMU_ROOT/configure" \
        --target-list=riscv32-softmmu \
        --without-default-features \
        --enable-tcg \
        --enable-tools \
        --enable-trace-backends=log \
        &> "$config_log" ;
    then
        echo "Failed (see $config_log)"
        exit 1
    fi
fi

# Build QEMU
build_log="$PWD/qemu_build.log"
echo "Building QEMU (output log in $build_log)..."
if ! ninja qemu-system-riscv32 &> "$build_log" ; then
    echo "Failed (see $build_log)"
    exit 1
fi
if ! ninja qemu-img &>> "$build_log" ; then
    echo "Failed (see $build_log)"
    exit 1
fi

# Run the make release script to create the requested archive.
# Some versions have a bug and except PWD to be the source directory.
archive_log="$PWD/qemu_archive.log"
echo "Creating archive (output log in $archive_log)..."
cd "$QEMU_ROOT"
if ! "./scripts/opentitan/make_release.sh" \
        "$OUT_ARCHIVE" . "build" &> "$archive_log" ;
then
    echo "Failed (see $archive_log)"
    exit 1
fi
