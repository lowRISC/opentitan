# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otp.bzl", "get_otp_images")
load("//rules:const.bzl", "KEY_AUTHENTICITY")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "bitstream",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream/universal:none"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_test_rom_hyp"],
        "//hw/bitstream:bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream/universal:none"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:cw310_hyperdebug_mmi"],
        "//hw/bitstream:bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_mmi"],
    }),
    tags = ["manual"],
)
