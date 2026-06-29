# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules/opentitan:exec_env.bzl", "bitstream_from_env", "memory_from_env")

package(default_visibility = ["//visibility:public"])

bitstream_from_env(
    name = "bitstream_fpga_hyper340",
    testonly = True,
    exec_env = "//hw/top_earlgrey:fpga_cw340_rom_ext",
    tags = ["manual"],
)

memory_from_env(
    name = "rom_fpga_hyper340",
    testonly = True,
    exec_env = "//hw/top_earlgrey:fpga_cw340_rom_ext",
    memory = "rom",
    tags = ["manual"],
)

memory_from_env(
    name = "otp_fpga_hyper340",
    testonly = True,
    exec_env = "//hw/top_earlgrey:fpga_cw340_rom_ext",
    memory = "otp",
    tags = ["manual"],
)

pkg_files(
    name = "bitstreams",
    testonly = True,
    srcs = [
        ":bitstream_fpga_hyper340",
    ],
    tags = ["manual"],
)

pkg_filegroup(
    name = "bitstreams_pkg",
    testonly = True,
    srcs = [
        ":bitstreams",
    ],
    prefix = "earlgrey/bitstreams",
    tags = ["manual"],
)

pkg_files(
    name = "fpga_hyper340_memories",
    testonly = True,
    srcs = [
        ":otp_fpga_hyper340",
        ":rom_fpga_hyper340",
    ],
    tags = ["manual"],
)

pkg_filegroup(
    name = "memories_pkg",
    testonly = True,
    srcs = [
        ":fpga_hyper340_memories",
    ],
    prefix = "earlgrey/memories",
    tags = ["manual"],
)

pkg_files(
    name = "bazel",
    srcs = [
        "build_bazel",
        "module_bazel",
    ],
    renames = {
        "build_bazel": "BUILD.bazel",
        "module_bazel": "MODULE.bazel",
    },
)

pkg_tar(
    name = "devbundle",
    testonly = True,
    srcs = [
        ":bazel",
        ":bitstreams_pkg",
        ":memories_pkg",
        "//hw:package",
        "//hw/top_earlgrey/data/otp:package",
        "//sw/device/lib/testing/test_rom:package",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:fpga_dev_pkg",
        "//sw/device/silicon_creator/rom_ext:fpga_dev_pkg",
        "//sw/host/opentitantool:package",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:openocd_bin",
    ],
    extension = "tar.xz",
    tags = ["manual"],
)
