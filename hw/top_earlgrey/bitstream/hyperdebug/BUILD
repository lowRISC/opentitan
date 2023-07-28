# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:splice.bzl", "bitstream_splice")
load("//rules:otp.bzl", "get_otp_images")
load("//rules:const.bzl", "KEY_AUTHENTICITY")
load(
    "//rules:bitstreams_select.bzl",
    "bitstream_cache_filter",
    "bitstream_cache_or",
)

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "test_rom",
    testonly = True,
    srcs = select({
        "//hw/top_earlgrey/bitstream:bitstream_skip": ["//hw/bitstream:skip"],
        "//hw/top_earlgrey/bitstream:bitstream_vivado": ["//hw/top_earlgrey/bitstream/vivado:fpga_cw310_test_rom"],
        "//hw/top_earlgrey/bitstream:bitstream_gcp_splice": [":gcp_spliced_test_rom"],
        "//conditions:default": [":gcp_spliced_test_rom"],
    }),
    tags = ["manual"],
)

[
    filegroup(
        name = "rom_with_{}_keys".format(authenticity),
        testonly = True,
        srcs = select({
            "//hw/top_earlgrey/bitstream:bitstream_skip": ["//hw/bitstream:skip"],
            "//hw/top_earlgrey/bitstream:bitstream_vivado": ["//hw/top_earlgrey/bitstream/vivado:fpga_cw310_rom_with_{}_keys".format(authenticity)],
            "//hw/top_earlgrey/bitstream:bitstream_gcp_splice": [":gcp_spliced_rom_with_{}_fake_keys".format(authenticity)],
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
        "//hw/top_earlgrey/bitstream:bitstream_skip": ["//hw/bitstream:skip"],
        "//hw/top_earlgrey/bitstream:bitstream_vivado": ["//hw/top_earlgrey/bitstream/vivado:rom_mmi"],
        "//conditions:default": bitstream_cache_or(
            "chip_earlgrey_cw310_hyperdebug",
            ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_rom_mmi"],
            ["//hw/top_earlgrey/bitstream/vivado:rom_mmi_hyp"],
        ),
    }),
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    testonly = True,
    srcs = select({
        "//hw/top_earlgrey/bitstream:bitstream_skip": ["//hw/bitstream:skip"],
        "//hw/top_earlgrey/bitstream:bitstream_vivado": ["//hw/top_earlgrey/bitstream/vivado:otp_mmi"],
        "//conditions:default": bitstream_cache_or(
            "chip_earlgrey_cw310_hyperdebug",
            ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_rom_mmi"],
            ["//hw/top_earlgrey/bitstream/vivado:rom_mmi_hyp"],
        ),
    }),
    tags = ["manual"],
)

[
    filegroup(
        name = "rom_with_{}_keys_otp_{}".format(authenticity, otp_name),
        testonly = True,
        srcs = select({
            "//hw/top_earlgrey/bitstream:bitstream_skip": ["//hw/bitstream:skip"],
            "//hw/top_earlgrey/bitstream:bitstream_vivado": ["//hw/top_earlgrey/bitstream/vivado:fpga_cw310_rom_with_{}_keys_otp_{}".format(authenticity, otp_name)],
            "//hw/top_earlgrey/bitstream:bitstream_gcp_splice": [":gcp_spliced_rom_with_{}_keys_otp_{}".format(authenticity, otp_name)],
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
    src = bitstream_cache_or(
        "chip_earlgrey_cw310_hyperdebug",
        "@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream",
        "//hw/top_earlgrey/bitstream/vivado:fpga_cw310_test_rom_hyp",
    ),
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
        src = bitstream_cache_or(
            "chip_earlgrey_cw310_hyperdebug",
            "@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream",
            "//hw/top_earlgrey/bitstream/vivado:fpga_cw310_test_rom_hyp",
        ),
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
