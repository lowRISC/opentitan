# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

AC_RANGE_CHECK = opentitan_ip(
    name = "ac_range_check",
    hjson = "@lowrisc_opentitan//hw/top_darjeeling/ip_autogen/ac_range_check/data:ac_range_check.hjson",
    ipconfig = "@lowrisc_opentitan//hw/top_darjeeling/ip_autogen/ac_range_check/data:top_darjeeling_ac_range_check.ipconfig.hjson",
)
