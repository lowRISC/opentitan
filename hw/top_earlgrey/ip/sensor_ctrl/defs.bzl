# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

SENSOR_CTRL = opentitan_ip(
    name = "sensor_ctrl",
    hjson = "//hw/top_earlgrey/ip/sensor_ctrl/data:sensor_ctrl.hjson",
)
