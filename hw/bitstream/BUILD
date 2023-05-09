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
# * `--define bitstream=local` causes these targets to use a local
#   (pre-existing) bitstream, and splice in a locally-built ROM image or OTP. To
#   use this feature, three files must be present in $REPO_TOP/hw/bitstream/,
#   including:
#     - a bitstream file named: `local_chip_earlgrey_cw310.bit`
#     - a ROM MMI file named: `local_rom.mmi`
#     - an OTP MMI file named: `local_otp.mmi`
#
# Downstream targets will see the effects of this caching logic. For example,
# specifying `--define bitstream=vivado` when testing
# //sw/device/silicon_creator/lib/drivers:hmac_functest_fpga_cw310 will turn
# `:test_rom` into a full Vivado bitstream build.

exports_files([
    "local_chip_earlgrey_cw310.bit",
    "local_rom.mmi",
    "local_otp.mmi",
])

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

config_setting(
    name = "bitstream_local_splice",
    define_values = {
        "bitstream": "local",
    },
)

filegroup(
    name = "test_rom",
    testonly = True,
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_test_rom"],
        "bitstream_gcp_splice": [":gcp_spliced_test_rom"],
        "bitstream_local_splice": [":local_spliced_test_rom"],
        "//conditions:default": [":gcp_spliced_test_rom"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "rom",
    testonly = True,
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_rom"],
        "bitstream_gcp_splice": [":gcp_spliced_rom"],
        "bitstream_local_splice": [":local_spliced_rom"],
        "//conditions:default": [":gcp_spliced_rom"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "rom_mmi",
    testonly = True,
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:rom_mmi"],
        "bitstream_local_splice": [":local_rom.mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_rom_mmi"],
    }),
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    testonly = True,
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:otp_mmi"],
        "bitstream_local_splice": [":local_otp.mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_otp_mmi"],
    }),
    tags = ["manual"],
)

[
    filegroup(
        name = "rom_otp_" + otp_name,
        testonly = True,
        srcs = select({
            "bitstream_skip": ["skip.bit"],
            "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_rom_otp_" + otp_name],
            "bitstream_gcp_splice": [":gcp_spliced_rom_otp_" + otp_name],
            "bitstream_local_splice": [":local_spliced_rom_otp_" + otp_name],
            "//conditions:default": [":gcp_spliced_rom_otp_" + otp_name],
        }),
        tags = ["manual"],
    )
    for (otp_name, _) in get_otp_images()
]

# Build the Test ROM and splice it into a local bitstream.
bitstream_splice(
    name = "local_spliced_test_rom",
    testonly = True,
    src = ":local_chip_earlgrey_cw310.bit",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# Build the ROM and splice it into a local bitstream.
bitstream_splice(
    name = "local_spliced_rom",
    testonly = True,
    src = ":local_chip_earlgrey_cw310.bit",
    data = "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# Splice OTP images into the locally-spliced ROM bitstream (created from a local bitstream).
[
    bitstream_splice(
        name = "local_spliced_rom_otp_" + otp_name,
        testonly = True,
        src = ":local_spliced_rom",
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for (otp_name, img_target) in get_otp_images()
]

# Build the Test ROM and splice it into a cached bitstream.
bitstream_splice(
    name = "gcp_spliced_test_rom",
    testonly = True,
    src = "@bitstreams//:chip_earlgrey_cw310_bitstream",
    data = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# Build the ROM and splice it into a cached bitstream.
bitstream_splice(
    name = "gcp_spliced_rom",
    testonly = True,
    src = "@bitstreams//:chip_earlgrey_cw310_bitstream",
    data = "//sw/device/silicon_creator/rom:rom_with_fake_keys_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
    update_usr_access = True,
    visibility = ["//visibility:private"],
)

# Splice OTP images into the locally-spliced ROM bitstream.
[
    bitstream_splice(
        name = "gcp_spliced_rom_otp_" + otp_name,
        testonly = True,
        src = ":gcp_spliced_rom",
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
        visibility = ["//visibility:private"],
    )
    for (otp_name, img_target) in get_otp_images()
]
