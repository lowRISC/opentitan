# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:splice.bzl", universal_splice = "bitstream_splice")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "none",
    srcs = ["skip.bit"],
)

label_flag(
    name = "rom",
    build_setting_default = ":none",
)

label_flag(
    name = "otp",
    build_setting_default = ":none",
)

label_flag(
    name = "env",
    build_setting_default = ":none",
)

universal_splice(
    name = "splice",
    testonly = True,
    # When the src bitstream, rom_mmi and otp_mmi fields are empty,
    # the rule will use values from the exec_env.
    exec_env = ":env",
    otp = ":otp",
    rom = ":rom",
    tags = ["manual"],
)
