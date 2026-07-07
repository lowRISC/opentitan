# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "bool_flag")
load("@rules_cc//cc:defs.bzl", "cc_library")

package(default_visibility = ["//visibility:public"])

# Bazel build flags to control library selection.
# Set --@lowrisc_opentitan//third_party/host_libs:use_local_udev=True
# to force compiling the library from source instead of using the host system's library.
bool_flag(
    name = "use_local_udev",
    build_setting_default = False,
)

config_setting(
    name = "local_udev_requested",
    flag_values = {":use_local_udev": "True"},
)

bool_flag(
    name = "use_local_usb",
    build_setting_default = False,
)

config_setting(
    name = "local_usb_requested",
    flag_values = {":use_local_usb": "True"},
)

bool_flag(
    name = "use_local_ftdi",
    build_setting_default = False,
)

config_setting(
    name = "local_ftdi_requested",
    flag_values = {":use_local_ftdi": "True"},
)

bool_flag(
    name = "use_local_ssl",
    build_setting_default = False,
)

config_setting(
    name = "local_ssl_requested",
    flag_values = {":use_local_ssl": "True"},
)

bool_flag(
    name = "use_local_crypto",
    build_setting_default = False,
)

config_setting(
    name = "local_crypto_requested",
    flag_values = {":use_local_crypto": "True"},
)

# Public redirection alias. Downstream modules should refer to this
# target (via @lowrisc_opentitan//third_party/host_libs:udev) to get
# the correct library depending on flags.
alias(
    name = "udev",
    actual = "@host_libs//:udev",
)

alias(
    name = "usb",
    actual = "@host_libs//:usb",
)

alias(
    name = "ftdi",
    actual = "@host_libs//:ftdi",
)

alias(
    name = "ssl",
    actual = "@host_libs//:ssl",
)

alias(
    name = "crypto",
    actual = "@host_libs//:crypto",
)

# OpenSSL target that combines ssl and crypto.
# Downstream rust crates should depend on this.
cc_library(
    name = "openssl",
    deps = [
        ":crypto",
        ":ssl",
    ],
)

# Failure target for missing local OpenSSL fallback.
# This will fail to compile if local OpenSSL is requested.
cc_library(
    name = "openssl_local_fallback_fail",
    srcs = ["missing_local_openssl_fallback.c"],
)

exports_files(["empty.pc"])
