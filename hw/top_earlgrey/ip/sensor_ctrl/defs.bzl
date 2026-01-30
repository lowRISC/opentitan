# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

SENSOR_CTRL = opentitan_ip(
    name = "sensor_ctrl",
    hjson = "@lowrisc_opentitan//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl.hjson",
)
