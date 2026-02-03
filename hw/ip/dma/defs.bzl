# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

DMA = opentitan_ip(
    name = "dma",
    hjson = "@lowrisc_opentitan//hw/ip/dma/data:dma.hjson",
)
