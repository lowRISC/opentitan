# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:autogen.bzl", "opentitan_autogen_isr_testutils")
load("//sw/device/lib/dif:defs.bzl", "IPS_WITHOUT_DIF")

package(default_visibility = ["//visibility:public"])

opentitan_autogen_isr_testutils(
    name = "isr_testutils",
    exclude_ips = IPS_WITHOUT_DIF,
    top = "//hw/top:top_desc",
)
