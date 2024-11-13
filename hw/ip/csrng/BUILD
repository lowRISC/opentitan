# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:hw.bzl", "opentitan_ip")

package(default_visibility = ["//visibility:public"])

opentitan_ip(
    name = "csrng",
    files = glob(["**"]),
    hjson = "//hw/ip/csrng/data:hjson",
)
