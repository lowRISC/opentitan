# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The targets in this files are designed so that bazel will not complain
# about missing bitstreams targets but if you actually try to use them
# then an error will be thrown. This is useful for offline builds to
# load bitstreams from the cache but avoid Vivado builds in case of mistake.

load("//rules:bitstreams.bzl", "unavailable_bitstream")

package(default_visibility = ["//visibility:public"])

# Note: all of the targets are tagged with "manual" to prevent them from being
# matched by bazel wildcards like "//...".  In order to build the bitstream,
# you need to ask for it directly or by dependency via another rule, such as
# a functest.
unavailable_bitstream(
    name = "fpga_cw310_test_rom",
    rom_mmi = "rom_mmi",
    otp_mmi = "otp_mmi",
)

# Standalone CW310 image for use with hyperdebug.
unavailable_bitstream(
    name = "fpga_cw310_test_rom_hyp",
    rom_mmi = "rom_mmi_hyp",
    otp_mmi = "otp_mmi_hyp",
)

# CW340 bitstream
unavailable_bitstream(
    name = "fpga_cw340_test_rom",
    rom_mmi = "fpga_cw340_rom_mmi",
    otp_mmi = "fpga_cw340_otp_mmi",
)
