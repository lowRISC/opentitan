# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:splice.bzl", "bitstream_splice")
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
    name = "rom_mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream/universal:none"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:rom_mmi_hyp"],
        "//hw/bitstream:bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_rom_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_rom_mmi"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    testonly = True,
    srcs = select({
        "//hw/bitstream:bitstream_skip": ["//hw/bitstream/universal:none"],
        "//hw/bitstream:bitstream_vivado": ["//hw/bitstream/vivado:otp_mmi_hyp"],
        "//hw/bitstream:bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_otp_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_hyperdebug_otp_mmi"],
    }),
    tags = ["manual"],
)

# Build the Test ROM and splice it into the bitstream.
bitstream_splice(
    name = "test_rom",
    testonly = True,
    src = ":bitstream",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
)

# Build the ROM and splice it into a cached bitstream.
[
    bitstream_splice(
        name = "rom_with_{}_keys".format(authenticity),
        testonly = True,
        src = ":bitstream",
        data = "//sw/device/silicon_creator/rom:rom_with_{}_keys_fpga_cw310_scr_vmem".format(authenticity),
        meminfo = ":rom_mmi",
        tags = ["manual"],
        update_usr_access = True,
    )
    for authenticity in KEY_AUTHENTICITY
]

# Splice OTP images into the locally-spliced ROM bitstream.
[
    bitstream_splice(
        name = "rom_with_{}_keys_otp_{}".format(authenticity, otp_name),
        testonly = True,
        src = ":rom_with_{}_keys".format(authenticity),
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
    )
    for (otp_name, img_target) in get_otp_images()
    for authenticity in KEY_AUTHENTICITY
]

# TODO(#20231): Remove once support for new splicing infrastructure is
# available.
[
    bitstream_splice(
        name = "rom_with_{}_keys_otp_{}".format(authenticity, otp_name),
        testonly = True,
        src = ":rom_with_{}_keys".format(authenticity),
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
    )
    for (otp_name, img_target) in [
        ("sival_test_locked0", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_post_cp_test_locked0"),
        ("sival_prod_personalized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_personalized"),
        ("sival_prod_end_personalized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_end_personalized"),
        ("sival_dev_individualized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_dev_individualized"),
        ("sival_dev_personalized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_dev_personalized"),
    ]
    for authenticity in KEY_AUTHENTICITY
]
