# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//rules:common_settings.bzl", "string_flag")

package(default_visibility = ["//visibility:public"])

label_flag(
    name = "token",
    build_setting_default = "//signing/tokens:local",
)

config_setting(
    name = "test_keys",
    flag_values = {
        ":token": "//signing/tokens:local",
    },
)

# TODO(#24641): Simplify key selection after eliminating RSA keys.
# The currently released ROM_EXT binary for ES silicon (version 0.4) supports
# only RSA keys.  The next release will eliminate RSA keys in favor of ECDSA
# keys.  In order to allow current users to continue to build RSA-signed
# applications (e.g. tests), we default to an `owner_key_type` of RSA.  Ad-hoc
# testing on ES DEV parts running the as-yet unreleased ROM_EXT (at the head
# of this branch) can select ECDSA keys.
#
# Note that the FPGA targets always run the ROM_EXT from head, and always
# select an ECDSA key regardless of the `owner_key_type` setting.
#
# This key-type selection will be removed when we finish converting to ECDSA
# and eliminate RSA keys for application signing.
string_flag(
    name = "owner_key_type",
    build_setting_default = "ecdsa",
    values = [
        "rsa",
        "ecdsa",
    ],
)

config_setting(
    name = "owner_key_rsa",
    flag_values = {":owner_key_type": "rsa"},
)

config_setting(
    name = "owner_key_ecdsa",
    flag_values = {":owner_key_type": "ecdsa"},
)

config_setting(
    name = "test_keys_rsa",
    flag_values = {
        ":token": "//signing/tokens:local",
        ":owner_key_type": "rsa",
    },
)

config_setting(
    name = "test_keys_ecdsa",
    flag_values = {
        ":token": "//signing/tokens:local",
        ":owner_key_type": "ecdsa",
    },
)

filegroup(
    name = "none_key",
    srcs = ["skip.bit"],
)
