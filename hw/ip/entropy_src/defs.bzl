# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

ENTROPY_SRC = opentitan_ip(
    name = "entropy_src",
    hjson = "@lowrisc_opentitan//hw/ip/entropy_src/data:entropy_src.hjson",
)
