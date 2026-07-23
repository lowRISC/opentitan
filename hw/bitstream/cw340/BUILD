# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otp.bzl", "get_otp_images")

# We do not have a signed CW340 ROM yet.
KEY_AUTHENTICITY = [
    "fake",
]

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "bitstream",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream/universal:none"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw340_test_rom"],
        # All other cases are handled by the bitstream cache.
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw340_bitstream"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream/universal:none"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:cw340_mmi"],
        # All other cases are handled by the bitstream cache.
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw340_mmi"],
    }),
    tags = ["manual"],
)
