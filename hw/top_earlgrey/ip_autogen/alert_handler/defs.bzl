# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

ALERT_HANDLER = opentitan_ip(
    name = "alert_handler",
    hjson = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/alert_handler/data:alert_handler.hjson",
)
