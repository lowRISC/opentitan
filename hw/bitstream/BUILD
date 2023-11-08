# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_pkg//pkg:mappings.bzl", "pkg_files")
load("//rules:splice.bzl", "bitstream_splice")
load("//rules:otp.bzl", "get_otp_images")
load("//rules:const.bzl", "KEY_AUTHENTICITY")
load("//rules:bitstreams.bzl", "bitstream_fragment_from_manifest")

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
    name = "bitstream",
    testonly = True,
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_test_rom"],
        "bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_bitstream"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_bitstream"],
    }),
    tags = ["manual"],
    visibility = ["//visibility:private"],
)

filegroup(
    name = "rom_mmi",
    testonly = True,
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:rom_mmi"],
        "bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_rom_mmi"],
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
        "bitstream_gcp_splice": ["@bitstreams//:chip_earlgrey_cw310_otp_mmi"],
        "//conditions:default": ["@bitstreams//:chip_earlgrey_cw310_otp_mmi"],
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
        src = "//hw/bitstream/hyperdebug:rom_with_{}_keys".format(authenticity),
        data = img_target,
        meminfo = "//hw/bitstream/hyperdebug:otp_mmi",
        tags = ["manual"],
        update_usr_access = True,
    )
    for (otp_name, img_target) in [
        ("sival_prod_personalized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_personalized"),
        ("sival_prod_end_personalized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_prod_end_personalized"),
        ("sival_dev_personalized", "//hw/ip/otp_ctrl/data/earlgrey_a0_skus/sival:otp_img_dev_personalized"),
    ]
    for authenticity in KEY_AUTHENTICITY
]

# Create manifest fragments for all the cached bitstreams
bitstream_fragment_from_manifest(
    name = "chip_earlgrey_cw310_cached_fragment",
    srcs = [
        "@bitstreams//:chip_earlgrey_cw310_bitstream",
        "@bitstreams//:chip_earlgrey_cw310_otp_mmi",
        "@bitstreams//:chip_earlgrey_cw310_rom_mmi",
    ],
    design = "chip_earlgrey_cw310",
    manifest = "@bitstreams//:manifest",
    tags = ["manual"],
)

pkg_tar(
    name = "chip_earlgrey_cw310_cached_archive",
    testonly = True,
    srcs = [":chip_earlgrey_cw310_cached_fragment"],
    mode = "0444",
    package_dir = "build-bin/hw/top_earlgrey/chip_earlgrey_cw310",
    strip_prefix = "/hw/bitstream/chip_earlgrey_cw310_cached_fragment",
    tags = ["manual"],
)

bitstream_fragment_from_manifest(
    name = "chip_earlgrey_cw310_hyperdebug_cached_fragment",
    srcs = [
        "@bitstreams//:chip_earlgrey_cw310_hyperdebug_bitstream",
        "@bitstreams//:chip_earlgrey_cw310_hyperdebug_otp_mmi",
        "@bitstreams//:chip_earlgrey_cw310_hyperdebug_rom_mmi",
    ],
    design = "chip_earlgrey_cw310_hyperdebug",
    manifest = "@bitstreams//:manifest",
    tags = ["manual"],
)

pkg_tar(
    name = "chip_earlgrey_cw310_hyperdebug_cached_archive",
    testonly = True,
    srcs = [":chip_earlgrey_cw310_hyperdebug_cached_fragment"],
    mode = "0444",
    package_dir = "build-bin/hw/top_earlgrey/chip_earlgrey_cw310_hyperdebug",
    strip_prefix = "/hw/bitstream/chip_earlgrey_cw310_hyperdebug_cached_fragment",
    tags = ["manual"],
)

bitstream_fragment_from_manifest(
    name = "chip_earlgrey_cw340_cached_fragment",
    srcs = [
        "@bitstreams//:chip_earlgrey_cw340_bitstream",
        "@bitstreams//:chip_earlgrey_cw340_otp_mmi",
        "@bitstreams//:chip_earlgrey_cw340_rom_mmi",
    ],
    design = "chip_earlgrey_cw340",
    manifest = "@bitstreams//:manifest",
    tags = ["manual"],
)

pkg_tar(
    name = "chip_earlgrey_cw340_cached_archive",
    testonly = True,
    srcs = [":chip_earlgrey_cw340_cached_fragment"],
    mode = "0444",
    package_dir = "build-bin/hw/top_earlgrey/chip_earlgrey_cw340",
    strip_prefix = "/hw/bitstream/chip_earlgrey_cw340_cached_fragment",
    tags = ["manual"],
)

# Packaging rule for spliced bitstreams
pkg_files(
    name = "package",
    testonly = True,
    srcs = [
        ":rom_with_{}_keys".format(authenticity)
        for authenticity in KEY_AUTHENTICITY
    ] + [
        ":rom_with_{}_keys_otp_{}".format(authenticity, otp_name)
        for (otp_name, _) in get_otp_images()
        for authenticity in KEY_AUTHENTICITY
    ],
    prefix = "earlgrey/fpga_cw310/standard",
    tags = ["manual"],
)
