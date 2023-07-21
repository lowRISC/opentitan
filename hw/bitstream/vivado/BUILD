# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules:const.bzl", "KEY_AUTHENTICITY")
load("//rules:fusesoc.bzl", "fusesoc_build")
load("//rules:otp.bzl", "get_otp_images")
load("//rules:splice.bzl", "bitstream_splice")
load("//rules:const.bzl", "KEY_AUTHENTICITY")
load("//rules:bitstreams.bzl", "bitstream_manifest_fragment")

package(default_visibility = ["//visibility:public"])

# The readmem directives in the fusesoc-ized build tree will be in the subdir
# ${build_root}/src/lowrisc_prim_util_memload_0/rtl/prim_util_memload.svh,
# and ${build_root} will be a subdirectory called `build.fpga_cw310` inside of
# bazel-out/k8-{configname}/bin/hw/bitstream/vivado.
# Therefore, the relative path between prim_util_memload.svh and the project-root
# relative $(location ...) resolved labels is up 10 subdirectories.
_PREFIX = "../../../../../../../../../.."

_FPGA_CW310_TESTROM = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw310_scr_vmem"

_FPGA_CW310_OTP_RMA = "//hw/ip/otp_ctrl/data:img_rma"

_FPGA_CW310_TESTROM_PATH = "{}/$(location {})".format(_PREFIX, _FPGA_CW310_TESTROM)

_FPGA_CW310_OTP_RMA_PATH = "{}/$(location {})".format(_PREFIX, _FPGA_CW310_OTP_RMA)

# Note: all of the targets are tagged with "manual" to prevent them from being
# matched by bazel wildcards like "//...".  In order to build the bitstream,
# you need to ask for it directly or by dependency via another rule, such as
# a functest.
fusesoc_build(
    name = "fpga_cw310",
    testonly = True,
    srcs = [
        "//hw:all_files",
        _FPGA_CW310_TESTROM,
        _FPGA_CW310_OTP_RMA,
    ],
    cores = ["//:cores"],
    data = ["//hw/ip/otbn:all_files"],
    flags = [
        "--BootRomInitFile=" + _FPGA_CW310_TESTROM_PATH,
        "--OtpCtrlMemInitFile=" + _FPGA_CW310_OTP_RMA_PATH,
    ],
    output_groups = {
        "bitstream": ["synth-vivado/lowrisc_systems_chip_earlgrey_cw310_0.1.bit"],
        "rom_mmi": ["synth-vivado/rom.mmi"],
        "otp_mmi": ["synth-vivado/otp.mmi"],
    },
    systems = ["lowrisc:systems:chip_earlgrey_cw310"],
    tags = ["manual"],
    target = "synth",
)

filegroup(
    name = "fpga_cw310_test_rom",
    testonly = True,
    srcs = [":fpga_cw310"],
    output_group = "bitstream",
    tags = ["manual"],
)

filegroup(
    name = "rom_mmi",
    testonly = True,
    srcs = [":fpga_cw310"],
    output_group = "rom_mmi",
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    testonly = True,
    srcs = [":fpga_cw310"],
    output_group = "otp_mmi",
    tags = ["manual"],
)

[
    bitstream_splice(
        name = "fpga_cw310_rom_with_{}_keys".format(authenticity),
        testonly = True,
        src = "@bitstreams//:chip_earlgrey_cw310_bitstream",
        data = "//sw/device/silicon_creator/rom:rom_with_{}_keys_fpga_cw310_scr_vmem".format(authenticity),
        meminfo = ":rom_mmi",
        tags = ["manual"],
    )
    for authenticity in KEY_AUTHENTICITY
]

# Splice OTP images into the ROM bitstream.
[
    bitstream_splice(
        name = "fpga_cw310_rom_with_{}_keys_otp_{}".format(authenticity, otp_name),
        testonly = True,
        src = ":fpga_cw310_rom_with_{}_keys".format(authenticity),
        data = img_target,
        meminfo = ":otp_mmi",
        tags = ["manual"],
    )
    for (otp_name, img_target) in get_otp_images()
    for authenticity in KEY_AUTHENTICITY
]

# Standalone CW310 image for use with hyperdebug.
fusesoc_build(
    name = "fpga_cw310_hyperdebug",
    testonly = True,
    srcs = [
        "//hw:all_files",
        _FPGA_CW310_TESTROM,
        _FPGA_CW310_OTP_RMA,
    ],
    cores = ["//:cores"],
    data = ["//hw/ip/otbn:all_files"],
    flags = [
        "--BootRomInitFile=" + _FPGA_CW310_TESTROM_PATH,
        "--OtpCtrlMemInitFile=" + _FPGA_CW310_OTP_RMA_PATH,
    ],
    output_groups = {
        "bitstream": ["synth-vivado/lowrisc_systems_chip_earlgrey_cw310_hyperdebug_0.1.bit"],
        "rom_mmi": ["synth-vivado/rom.mmi"],
        "otp_mmi": ["synth-vivado/otp.mmi"],
    },
    systems = ["lowrisc:systems:chip_earlgrey_cw310_hyperdebug"],
    tags = ["manual"],
    target = "synth",
)

filegroup(
    name = "fpga_cw310_test_rom_hyp",
    testonly = True,
    srcs = [":fpga_cw310_hyperdebug"],
    output_group = "bitstream",
    tags = ["manual"],
)

filegroup(
    name = "rom_mmi_hyp",
    testonly = True,
    srcs = [":fpga_cw310_hyperdebug"],
    output_group = "rom_mmi",
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi_hyp",
    testonly = True,
    srcs = [":fpga_cw310_hyperdebug"],
    output_group = "otp_mmi",
    tags = ["manual"],
)

# Bitstream cache manifest fragment targets
bitstream_manifest_fragment(
    name = "earlgrey_cw310_manifest",
    testonly = True,
    srcs = [":fpga_cw310"],
    bitstream = "bitstream",
    design = "chip_earlgrey_cw310",
    memory_maps = {
        "rom_mmi": "rom",
        "otp_mmi": "otp",
    },
    tags = ["manual"],
)

pkg_tar(
    name = "earlgrey_cw310_archive",
    testonly = True,
    srcs = [":earlgrey_cw310_manifest"],
    mode = "0444",
    package_dir = "build-bin/hw/top_earlgrey/chip_earlgrey_cw310",
    strip_prefix = "/hw/bitstream/vivado/earlgrey_cw310_manifest",
    tags = ["manual"],
)

bitstream_manifest_fragment(
    name = "earlgrey_cw310_hyperdebug_manifest",
    testonly = True,
    srcs = [":fpga_cw310_hyperdebug"],
    bitstream = "bitstream",
    design = "chip_earlgrey_cw310_hyperdebug",
    memory_maps = {
        "rom_mmi": "rom",
        "otp_mmi": "otp",
    },
    tags = ["manual"],
)

pkg_tar(
    name = "earlgrey_cw310_hyperdebug_archive",
    testonly = True,
    srcs = [":earlgrey_cw310_hyperdebug_manifest"],
    mode = "0444",
    package_dir = "build-bin/hw/top_earlgrey/chip_earlgrey_cw310_hyperdebug",
    strip_prefix = "/hw/bitstream/vivado/earlgrey_cw310_hyperdebug_manifest",
    tags = ["manual"],
)

# Packaging rules for bitstreams
pkg_files(
    name = "standard",
    testonly = True,
    srcs = [
        ":fpga_cw310_rom_with_fake_keys",
        ":fpga_cw310_rom_with_real_keys",
        ":fpga_cw310_test_rom",
        ":otp_mmi",
        ":rom_mmi",
    ] + [
        ":fpga_cw310_rom_with_{}_keys_otp_{}".format(authenticity, otp_name)
        for (otp_name, _) in get_otp_images()
        for authenticity in KEY_AUTHENTICITY
    ],
    prefix = "earlgrey/fpga_cw310/standard",
    tags = ["manual"],
)

pkg_files(
    name = "hyperdebug",
    testonly = True,
    srcs = [
        ":fpga_cw310_hyperdebug_manifest",
    ],
    prefix = "earlgrey/fpga_cw310/hyperdebug",
    tags = ["manual"],
)

pkg_filegroup(
    name = "package",
    testonly = True,
    srcs = [
        ":hyperdebug",
        ":standard",
    ],
    tags = ["manual"],
)
