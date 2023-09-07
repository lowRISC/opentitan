# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:splice.bzl", "bitstream_splice")
load("//rules:otp.bzl", "get_otp_images")
load("//rules:const.bzl", "KEY_AUTHENTICITY")

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "test_rom",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream:skip.bit"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_test_rom"],
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
            "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_rom_with_{}_keys".format(authenticity)],
            "//hw/bitstream:bitstream_gcp_splice": [":gcp_spliced_rom_with_{}_keys".format(authenticity)],
            "//conditions:default": [":gcp_spliced_rom_with_{}_keys".format(authenticity)],
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
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:rom_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_rom_mmi"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["skip.bit"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:otp_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_otp_mmi"],
    }),
    tags = ["manual"],
)

[
    filegroup(
        name = "rom_with_{}_keys_otp_{}".format(authenticity, otp_name),
        testonly = True,
        srcs = select({
            "//hw/bitstream:bitstream_skip": ["skip.bit"],
            "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_rom_with_{}_keys_otp_{}".format(authenticity, otp_name)],
            "//hw/bitstream:bitstream_gcp_splice": [":gcp_spliced_rom_with_{}_keys_otp_{}".format(authenticity, otp_name)],
            "//conditions:default": [":gcp_spliced_rom_with_{}_keys_otp_{}".format(authenticity, otp_name)],
        }),
        tags = ["manual"],
    )
    for (otp_name, _) in get_otp_images()
    for authenticity in KEY_AUTHENTICITY
]

# Build the Test ROM and splice it into a cached bitstream.
bitstream_splice(
    name = "gcp_spliced_test_rom",
    testonly = True,
    src = "@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

[
    bitstream_splice(
        name = "gcp_spliced_rom_with_{}_keys".format(authenticity),
        testonly = True,
        src = "@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream",
        data = "//sw/device/silicon_creator/rom:rom_with_{}_keys_fpga_cw310_scr_vmem".format(authenticity),
        meminfo = ":rom_mmi",
        tags = ["manual"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for authenticity in KEY_AUTHENTICITY
]

# Splice OTP images into the locally-spliced ROM bitstream.
[
    bitstream_splice(
        name = "gcp_spliced_rom_with_{}_keys_otp_{}".format(authenticity, otp_name),
        testonly = True,
        src = ":gcp_spliced_rom_with_{}_keys".format(authenticity),
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for (otp_name, img_target) in get_otp_images()
    for authenticity in KEY_AUTHENTICITY
]
