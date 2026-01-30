# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

PWM = opentitan_ip(
    name = "pwm",
    hjson = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/pwm/data:pwm.hjson",
    ipconfig = "@lowrisc_opentitan//hw/top_earlgrey/ip_autogen/pwm/data:top_earlgrey_pwm.ipconfig.hjson",
)
