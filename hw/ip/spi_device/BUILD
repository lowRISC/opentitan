# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "all_files",
    srcs = glob(["**"]) + [
        "//hw/ip/spi_device/data:all_files",
    ],
)

opentitan_ip(
    name = "spi_device",
    hjson = "//hw/ip/spi_device/data:hjson",
)
