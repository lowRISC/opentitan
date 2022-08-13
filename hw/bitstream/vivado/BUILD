# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")
load("//rules:fusesoc.bzl", "fusesoc_build")
load("//rules:splice.bzl", "bitstream_splice")

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
    srcs = [":fpga_cw310"],
    output_group = "bitstream",
    tags = ["manual"],
)

filegroup(
    name = "rom_mmi",
    srcs = [":fpga_cw310"],
    output_group = "rom_mmi",
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi",
    srcs = [":fpga_cw310"],
    output_group = "otp_mmi",
    tags = ["manual"],
)

bitstream_splice(
    name = "fpga_cw310_rom",
    src = ":fpga_cw310_test_rom",
    data = "//sw/device/silicon_creator/rom:rom_fpga_cw310_scr_vmem",
    meminfo = ":rom_mmi",
    tags = ["manual"],
)

# Splice in the dev OTP image, replacing the RMA image.
bitstream_splice(
    name = "fpga_cw310_rom_otp_dev",
    src = ":fpga_cw310_rom",
    data = "//hw/ip/otp_ctrl/data:img_dev",
    meminfo = ":otp_mmi",
    tags = ["manual"],
)

# Standalone CW310 image for use with hyperdebug.
fusesoc_build(
    name = "fpga_cw310_hyperdebug",
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
    srcs = [":fpga_cw310_hyperdebug"],
    output_group = "bitstream",
    tags = ["manual"],
)

filegroup(
    name = "rom_mmi_hyp",
    srcs = [":fpga_cw310_hyperdebug"],
    output_group = "rom_mmi",
    tags = ["manual"],
)

filegroup(
    name = "otp_mmi_hyp",
    srcs = [":fpga_cw310_hyperdebug"],
    output_group = "otp_mmi",
    tags = ["manual"],
)

# Packaging rules for bitstreams
pkg_files(
    name = "standard",
    srcs = [
        ":fpga_cw310_rom",
        ":fpga_cw310_rom_otp_dev",
        ":fpga_cw310_test_rom",
        ":otp_mmi",
        ":rom_mmi",
    ],
    prefix = "earlgrey/fpga_cw310/standard",
    tags = ["manual"],
)

pkg_files(
    name = "hyperdebug",
    srcs = [
        ":fpga_cw310_test_rom_hyp",
        ":otp_mmi_hyp",
        ":rom_mmi_hyp",
    ],
    prefix = "earlgrey/fpga_cw310/hyperdebug",
    tags = ["manual"],
)

pkg_filegroup(
    name = "package",
    srcs = [
        ":hyperdebug",
        ":standard",
    ],
    tags = ["manual"],
)
