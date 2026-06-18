# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules:const.bzl", "KEY_AUTHENTICITY")
load("//rules:fusesoc.bzl", "fusesoc_build")
load("//rules:otp.bzl", "get_otp_images")
load("//rules:bitstreams.bzl", "bitstream_manifest_fragment")

package(default_visibility = ["//visibility:public"])

# The readmem directives in the fusesoc-ized build tree will be in the subdir
# ${build_root}/${core}/${target}-${tool}/src/lowrisc_prim_util_memload_0/rtl/prim_util_memload.svh,
# and ${build_root} will be a subdirectory called `build.fpga_cw*` inside of
# bazel-out/k8-{configname}/bin/hw/bitstream/vivado.
# Therefore, the relative path between prim_util_memload.svh and the project-root
# relative $(location ...) resolved labels is up 10 subdirectories.
_PREFIX = "../../../../../../../../../../.."

_CW340_TESTROM = "//sw/device/lib/testing/test_rom:test_rom_fpga_cw340_scr_vmem"

_OTP_RMA = "//hw/top_earlgrey/data/otp:img_rma"

_CW340_TESTROM_PATH = "{}/$(location {})".format(_PREFIX, _CW340_TESTROM)

_OTP_RMA_PATH = "{}/$(location {})".format(_PREFIX, _OTP_RMA)

_FPGA_PATH_TMPL = "lowrisc_systems_{}_0.1/synth-vivado/{}"

# CW340 bitstream
fusesoc_build(
    name = "fpga_cw340",
    testonly = True,
    srcs = [
        "//hw:rtl_files",
        _CW340_TESTROM,
        _OTP_RMA,
    ],
    cores = ["//hw:cores"],
    data = ["//hw/ip/otbn:rtl_files"],
    flags = [
        "--BootRomInitFile=" + _CW340_TESTROM_PATH,
        "--OtpMacroMemInitFile=" + _OTP_RMA_PATH,
    ],
    output_groups = {
        "bitstream": [_FPGA_PATH_TMPL.format("chip_earlgrey_cw340", "lowrisc_systems_chip_earlgrey_cw340_0.1.bit")],
        "mmi": [_FPGA_PATH_TMPL.format("chip_earlgrey_cw340", "memories.mmi")],
        "logs": [_FPGA_PATH_TMPL.format("chip_earlgrey_cw340", "lowrisc_systems_chip_earlgrey_cw340_0.1.runs/")],
    },
    systems = ["lowrisc:systems:chip_earlgrey_cw340"],
    tags = ["manual"],
    target = "synth",
)

filegroup(
    name = "fpga_cw340_test_rom",
    testonly = True,
    srcs = [":fpga_cw340"],
    output_group = "bitstream",
    tags = ["manual"],
)

filegroup(
    name = "cw340_mmi",
    testonly = True,
    srcs = [":fpga_cw340"],
    output_group = "mmi",
    tags = ["manual"],
)

bitstream_manifest_fragment(
    name = "earlgrey_cw340_manifest",
    testonly = True,
    srcs = [":fpga_cw340"],
    bitstream = "bitstream",
    design = "chip_earlgrey_cw340",
    memories = [
        "rom",
        "otp",
        "flash0_info0",
        "flash0_info1",
        "flash0_info2",
        "flash1_info0",
        "flash1_info1",
        "flash1_info2",
    ],
    memory_map_file = ":cw340_mmi",
    tags = ["manual"],
)

pkg_tar(
    name = "earlgrey_cw340_archive",
    testonly = True,
    srcs = [":earlgrey_cw340_manifest"],
    mode = "0444",
    package_dir = "build-bin/hw/top_earlgrey/chip_earlgrey_cw340",
    strip_prefix = "/hw/bitstream/vivado/earlgrey_cw340_manifest",
    tags = ["manual"],
)
