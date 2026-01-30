# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

PINMUX = opentitan_ip(
    name = "pinmux",
    hjson = "@lowrisc_opentitan//hw/top_darjeeling/ip_autogen/pinmux/data:pinmux.hjson",
)
