# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

AES = opentitan_ip(
    name = "aes",
    hjson = "@lowrisc_opentitan//hw/ip/aes/data:aes.hjson",
)
