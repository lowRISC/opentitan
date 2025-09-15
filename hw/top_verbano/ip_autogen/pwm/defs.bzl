# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

PWM = opentitan_ip(
    name = "pwm",
    hjson = "//hw/top_verbano/ip_autogen/pwm/data:pwm.hjson",
    ipconfig = "//hw/top_verbano/ip_autogen/pwm/data:top_verbano_pwm.ipconfig.hjson",
)
