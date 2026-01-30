# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("@lowrisc_opentitan//rules/opentitan:hw.bzl", "opentitan_ip")

SPI_DEVICE = opentitan_ip(
    name = "spi_device",
    hjson = "@lowrisc_opentitan//hw/ip/spi_device/data:spi_device.hjson",
)
