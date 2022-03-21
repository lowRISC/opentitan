# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_binary(
    name = "spiflash",
    srcs = [
        "ftdi_spi_interface.cc",
        "ftdi_spi_interface.h",
        "spi_interface.h",
        "spiflash.cc",
        "updater.cc",
        "updater.h",
        "verilator_spi_interface.cc",
        "verilator_spi_interface.h",
    ],
    linkopts = [
        "-lftdi1",
    ],
    deps = [
        "//sw/host/vendor:mpsse",
        "//sw/vendor:cryptoc_sha256",
    ],
)
