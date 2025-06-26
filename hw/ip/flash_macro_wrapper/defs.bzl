# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:hw.bzl", "opentitan_ip")

FLASH_MACRO_WRAPPER = opentitan_ip(
    name = "flash_macro_wrapper",
    hjson = "//hw/ip/flash_macro_wrapper/data:flash_macro_wrapper.hjson",
)
