# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "bool_flag")
load("@host_libs//:status.bzl", "HAS_FTDI", "HAS_UDEV", "HAS_USB")

package(default_visibility = ["//visibility:public"])

exports_files(["pkgconfig_wrapper.sh"])

# Bazel build flags to control library selection.
# Set --@lowrisc_opentitan//third_party/host_libs:use_local_usb=True (etc.)
# to force compiling the library from source instead of using the host system's library.
bool_flag(
    name = "use_local_usb",
    build_setting_default = False,
)

bool_flag(
    name = "use_local_ftdi",
    build_setting_default = False,
)

bool_flag(
    name = "use_local_udev",
    build_setting_default = False,
)

config_setting(
    name = "local_usb_requested",
    flag_values = {":use_local_usb": "True"},
)

config_setting(
    name = "local_ftdi_requested",
    flag_values = {":use_local_ftdi": "True"},
)

config_setting(
    name = "local_udev_requested",
    flag_values = {":use_local_udev": "True"},
)

# Public aliases for consumers of the libraries (e.g. rust-sys crates or native C++ binaries).
# They automatically select the local build if:
# 1. The respective 'use_local_*' flag is set to True.
# 2. Or the host system does not have the library (fallback mode).
alias(
    name = "usb",
    actual = select({
        ":local_usb_requested": "@libusb_src//:libusb",
        "//conditions:default": "@host_libs//:usb" if HAS_USB else "@libusb_src//:libusb",
    }),
)

alias(
    name = "ftdi",
    actual = select({
        ":local_ftdi_requested": "@libftdi_src//:libftdi",
        "//conditions:default": "@host_libs//:ftdi" if HAS_FTDI else "@libftdi_src//:libftdi",
    }),
)

alias(
    name = "udev",
    actual = select({
        ":local_udev_requested": "@libudev_zero_src//:udev",
        "//conditions:default": "@host_libs//:udev" if HAS_UDEV else "@libudev_zero_src//:udev",
    }),
)

# Targets to extract or generate pkg-config (.pc) files for local builds.
#
# Crucially, we modify the 'prefix' variable in these generated .pc files to use
# '${pcfiledir}/../..'. This makes the pkg-config files relocatable, meaning they
# resolve paths relative to their own location inside the Bazel sandbox, rather
# than using absolute host paths.
filegroup(
    name = "libusb_gen_dir",
    srcs = ["@libusb_src//:libusb"],
    output_group = "gen_dir",
)

genrule(
    name = "local_usb_pc",
    srcs = [":libusb_gen_dir"],
    outs = ["local_pcs/libusb-1.0.pc"],
    cmd = """
    pc_file=$$(find $(location :libusb_gen_dir) -name "libusb-1.0.pc" | head -n 1)
    if [ -z "$$pc_file" ]; then
        echo "Error: libusb-1.0.pc not found" >&2
        exit 1
    fi
    mkdir -p $$(dirname $@)
    sed 's|^prefix=.*|prefix=$${pcfiledir}/../..|' $$pc_file > $@
    """,
)

filegroup(
    name = "libftdi_gen_dir",
    srcs = ["@libftdi_src//:libftdi"],
    output_group = "gen_dir",
)

genrule(
    name = "local_ftdi_pc",
    srcs = [":libftdi_gen_dir"],
    outs = ["local_pcs/libftdi1.pc"],
    cmd = """
    pc_file=$$(find $(location :libftdi_gen_dir) -name "libftdi1.pc" | head -n 1)
    if [ -z "$$pc_file" ]; then
        echo "Error: libftdi1.pc not found" >&2
        exit 1
    fi
    mkdir -p $$(dirname $@)
    sed 's|^prefix=.*|prefix=$${pcfiledir}/../..|' $$pc_file > $@
    """,
)

genrule(
    name = "local_udev_pc",
    srcs = ["@libudev_zero_src//:install_files"],
    outs = ["local_pcs/libudev.pc"],
    cmd = """
    mkdir -p $$(dirname $@)
    found=0
    for f in $(SRCS); do
        if [[ $$f == */libudev.pc ]]; then
            cp $$f $@
            found=1
            break
        fi
    done
    if [ $$found -eq 0 ]; then
        echo "Error: libudev.pc not found in SRCS" >&2
        exit 1
    fi
    """,
)

# Select .pc files
usb_pc = select({
    ":local_usb_requested": [":local_usb_pc"],
    "//conditions:default": ["@host_libs//:libusb-1.0.pc"] if HAS_USB else [":local_usb_pc"],
})

ftdi_pc = select({
    ":local_ftdi_requested": [":local_ftdi_pc"],
    "//conditions:default": ["@host_libs//:libftdi1.pc"] if HAS_FTDI else [":local_ftdi_pc"],
})

udev_pc = select({
    ":local_udev_requested": [":local_udev_pc"],
    "//conditions:default": ["@host_libs//:libudev.pc"] if HAS_UDEV else [":local_udev_pc"],
})

# Flattens all selected .pc files into a single directory ('pkgconfig/').
# This is necessary because 'pkg-config' expects to look for .pc files inside a
# single directory, and we want to point PKG_CONFIG_PATH to this directory.
genrule(
    name = "flat_pc_files",
    srcs = usb_pc + ftdi_pc + udev_pc,
    outs = [
        "pkgconfig/libusb-1.0.pc",
        "pkgconfig/libftdi1.pc",
        "pkgconfig/libudev.pc",
    ],
    cmd = """
    mkdir -p $(RULEDIR)/pkgconfig
    for f in $(SRCS); do
        filename=$$(basename $$f)
        cp $$f $(RULEDIR)/pkgconfig/$$filename
    done
    """,
)

filegroup(
    name = "pc_files",
    srcs = [":flat_pc_files"],
)
