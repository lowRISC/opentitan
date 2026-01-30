# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

ADC_CTRL = opentitan_ip(
    name = "adc_ctrl",
    hjson = "@lowrisc_opentitan//hw/ip/adc_ctrl/data:adc_ctrl.hjson",
)
