# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:splice.bzl", "bitstream_splice")
load("//rules:otp.bzl", "get_otp_images")

# We do not have a signed CW340 ROM yet.
KEY_AUTHENTICITY = [
    "fake",
]

package(default_visibility = ["//visibility:public"])

[
    bitstream_splice(
        name = "fpga_cw340_rom_with_{}_keys".format(authenticity),
        testonly = True,
        src = "//hw/bitstream/vivado:fpga_cw340_test_rom",
        data = "//sw/device/silicon_creator/rom:rom_with_{}_keys_fpga_cw340_scr_vmem".format(authenticity),
        meminfo = "//hw/bitstream/vivado:fpga_cw340_rom_mmi",
        tags = ["manual"],
        visibility = ["//visibility:private"],
    )
    for authenticity in KEY_AUTHENTICITY
]

bitstream_splice(
    name = "gcp_spliced_test_rom",
    testonly = True,
    src = "@bitstreams//:chip_earlgrey_cw340_bitstream",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw340_scr_vmem",
    meminfo = "@bitstreams//:chip_earlgrey_cw340_rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

[
    bitstream_splice(
        name = "gcp_spliced_rom_with_{}_keys".format(authenticity),
        testonly = True,
        src = "@bitstreams//:chip_earlgrey_cw340_bitstream",
        data = "//sw/device/silicon_creator/rom:rom_with_{}_keys_fpga_cw340_scr_vmem".format(authenticity),
        meminfo = "@bitstreams//:chip_earlgrey_cw340_rom_mmi",
        tags = ["manual"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for authenticity in KEY_AUTHENTICITY
]

filegroup(
    name = "test_rom",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream:skip.bit"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw340_test_rom"],
        "//hw/bitstream:bitstream_gcp_splice": [":gcp_spliced_test_rom"],
        "//conditions:default": [":gcp_spliced_test_rom"],
    }),
    tags = ["manual"],
)

[
    filegroup(
        name = "rom_with_{}_keys".format(authenticity),
        testonly = True,
        srcs = select({
            "//hw/bitstream:bitstream_skip": ["skip.bit"],
            "//hw/bitstream:bitstream_vivado": [":fpga_cw340_rom_with_{}_keys".format(authenticity)],
            "//hw/bitstream:bitstream_gcp_splice": [":gcp_spliced_rom_with_{}_keys".format(authenticity)],
            "//conditions:default": [":gcp_spliced_rom_with_fake_keys"],
        }),
        tags = ["manual"],
    )
    for authenticity in KEY_AUTHENTICITY
]

filegroup(
    name = "rom_mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["skip.bit"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw340_rom_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw340_rom_mmi"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["skip.bit"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw340_otp_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw340_otp_mmi"],
    }),
    tags = ["manual"],
)
