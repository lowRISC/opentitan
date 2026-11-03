# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

CHERIOT_MEM_SYS = opentitan_ip(
    name = "cheriot_mem_sys",
    hjson = "//hw/ip/cheriot_mem_sys/data:cheriot_mem_sys.hjson",
)
