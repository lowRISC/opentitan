# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:splice.bzl", "bitstream_splice")
load("//rules:otp.bzl", "get_otp_images")

package(default_visibility = ["//visibility:public"])

# By default, targets in this file will use cached artifacts from the GCP bucket
# instead of building them from scratch.
#
# You can control GCP bitstream selection with the BITSTREAM environment
# variable. See //rules:bitstreams.bzl for more information.
#
# Alternatively, you can disable or alter this caching behavior with the
# "bitstream" config setting.
#
# * `--define bitstream=skip` skips loading a bitstream into the FPGA. This is
#   useful if you already have a bitstream loaded into the FPGA and you don't
#   want the GCP cache manager to do anything unexpected.
#
# * `--define bitstream=vivado` causes these targets to build from scratch with
#   Vivado. You'll need to have Xilinx Vivado installed and have properly
#   configured access to a license or license server.
#
# * `--define bitstream=gcp_splice` causes these targets to use a cached
#   bitstream, but splice in a locally-built ROM image or OTP.
#
# Downstream targets will see the effects of this caching logic. For example,
# specifying `--define bitstream=vivado` when testing
# //sw/device/silicon_creator/lib/drivers:hmac_functest_fpga_cw310 will turn
# `:test_rom` into a full Vivado bitstream build.

config_setting(
    name = "bitstream_skip",
    define_values = {
        "bitstream": "skip",
    },
)

config_setting(
    name = "bitstream_vivado",
    define_values = {
        "bitstream": "vivado",
    },
)

config_setting(
    name = "bitstream_gcp_splice",
    define_values = {
        "bitstream": "gcp_splice",
    },
)

filegroup(
    name = "test_rom",
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_test_rom"],
        "bitstream_gcp_splice": [":gcp_spliced_test_rom"],
        "//conditions:default": ["@bitstreams//:bitstream_test_rom"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "rom",
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_rom"],
        "bitstream_gcp_splice": [":gcp_spliced_rom"],
        "//conditions:default": ["@bitstreams//:bitstream_rom"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "rom_mmi",
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:rom_mmi"],
        "//conditions:default": ["@bitstreams//:rom_mmi"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:otp_mmi"],
        "//conditions:default": ["@bitstreams//:otp_mmi"],
    }),
    tags = ["manual"],
)

[
    filegroup(
        name = "rom_otp_" + otp_name,
        srcs = select({
            "bitstream_skip": ["skip.bit"],
            "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_rom_otp_" + otp_name],
            "bitstream_gcp_splice": [":gcp_spliced_rom_otp_" + otp_name],

            # FIXME(#13807) By default, this will actually do a local splice
            # instead of retrieving the pre-spliced bitstream from the cache.
            # Before we cache OTP-spliced bitstreams, we need to work out the
            # details of the naming scheme.
            "//conditions:default": [":gcp_spliced_rom_otp_" + otp_name],
        }),
        tags = ["manual"],
    )
    for (otp_name, _) in get_otp_images()
]

# Build the Test ROM and splice it into a cached bitstream.
bitstream_splice(
    name = "gcp_spliced_test_rom",
    src = "@bitstreams//:bitstream_test_rom",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# Build the ROM and splice it into a cached bitstream.
bitstream_splice(
    name = "gcp_spliced_rom",
    src = "@bitstreams//:bitstream_test_rom",
    data = "//sw/device/silicon_creator/rom:rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# Splice OTP images into the locally-spliced ROM bitstream.
[
    bitstream_splice(
        name = "gcp_spliced_rom_otp_" + otp_name,
        src = ":gcp_spliced_rom",
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for (otp_name, img_target) in get_otp_images()
]
