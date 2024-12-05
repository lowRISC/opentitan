# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:defs.bzl", "OPENTITAN_PLATFORM")
load("//rules:stamp.bzl", "stamp_flag")

package(default_visibility = ["//visibility:public"])

config_setting(
    name = "opentitan_platform",
    values = {"platforms": OPENTITAN_PLATFORM},
)

# See stamp.bzl for explanation.
stamp_flag(name = "stamp_flag")
