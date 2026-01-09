# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:cc.bzl", "exec_env_filegroup")
load("//rules:files.bzl", "copy_files")

package(default_visibility = ["//visibility:public"])

copy_files(
    name = "copy_signed",
    testonly = True,
    srcs = [
        "//sw/device/silicon_creator/manuf/base:signed",
    ],
    filter = [
        "ft_personalize_sival",
    ],
    relative_to = ":BUILD",
    tags = ["manual"],
)

exec_env_filegroup(
    name = "ft_personalize_sival",
    testonly = True,
    exec_env = {
    },
    files = {
    },
)
