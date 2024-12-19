# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

SOC_PROXY = opentitan_ip(
    name = "soc_proxy",
    hjson = "//hw/top_darjeeling/ip/soc_proxy/data:soc_proxy.hjson",
)
