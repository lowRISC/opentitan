# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules:fusesoc.bzl", "fusesoc_build")
load("//rules:bitstreams.bzl", "bitstream_manifest_fragment")

_FPGA_PATH_TMPL = "lowrisc_systems_{}_0.1/synth-vivado/{}"

fusesoc_build(
    name = "fpga_cw305",
    testonly = True,
    srcs = [
        "//hw:rtl_files",
        "//hw/top_englishbreakfast:rtl_files",
    ],
    cores = ["//:cores"],
    output_groups = {
        "bitstream": [_FPGA_PATH_TMPL.format("chip_englishbreakfast_cw305", "lowrisc_systems_chip_englishbreakfast_cw305_0.1.bit")],
        "mmi": [_FPGA_PATH_TMPL.format("chip_englishbreakfast_cw305", "memories.mmi")],
        "logs": [_FPGA_PATH_TMPL.format("chip_englishbreakfast_cw305", "lowrisc_systems_chip_englishbreakfast_cw305_0.1.runs/")],
    },
    systems = ["lowrisc:systems:chip_englishbreakfast_cw305"],
    tags = ["manual"],
    target = "synth",
)

filegroup(
    name = "cw305_mmi",
    testonly = True,
    srcs = [":fpga_cw305"],
    output_group = "mmi",
    tags = ["manual"],
)

bitstream_manifest_fragment(
    name = "englishbreakfast_cw305_manifest",
    testonly = True,
    srcs = [":fpga_cw305"],
    bitstream = "bitstream",
    design = "chip_englishbreakfast_cw305",
    memories = [
        "rom",
    ],
    memory_map_file = ":cw305_mmi",
    tags = ["manual"],
)

pkg_tar(
    name = "englishbreakfast_cw305_archive",
    testonly = True,
    srcs = [":englishbreakfast_cw305_manifest"],
    mode = "0444",
    package_dir = "build-bin/hw/top_englishbreakfast/chip_englishbreakfast_cw305",
    strip_prefix = "/hw/top_englishbreakfast/bitstream/englishbreakfast_cw305_manifest",
    tags = ["manual"],
)
