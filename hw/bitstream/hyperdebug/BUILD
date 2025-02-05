# Copyright lowRISC contributors (OpenTitan project).
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

# Build the Test ROM and splice it into the bitstream.
bitstream_splice(
    name = "test_rom",
    testonly = True,
    src = ":bitstream",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    instance = "rom",
    meminfo = ":mmi",
    tags = ["manual"],
    update_usr_access = True,
)

# Build the ROM and splice it into a cached bitstream.
bitstream_splice(
    name = "mask_rom",
    testonly = True,
    src = ":bitstream",
    data = "//sw/device/silicon_creator/rom:mask_rom_fpga_cw310_scr_vmem",
    instance = "rom",
    meminfo = ":mmi",
    tags = ["manual"],
    update_usr_access = True,
)

# Splice OTP images into the locally-spliced ROM bitstream.
[
    bitstream_splice(
        name = "mask_rom_otp_{}".format(otp_name),
        testonly = True,
        src = ":mask_rom",
        data = img_target,
        instance = "otp",
        meminfo = ":mmi",
        tags = ["manual"],
        update_usr_access = True,
    )
    for (otp_name, img_target) in get_otp_images()
]
