# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

GPIO = opentitan_ip(
    name = "gpio",
    hjson = "//hw/top_earlgrey/ip_autogen/gpio/data:gpio.hjson",
    ipconfig = "//hw/top_earlgrey/ip_autogen/gpio/data:top_earlgrey_gpio.ipconfig.hjson",
)
