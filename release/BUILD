# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//third_party/github:rules.bzl", "release")

package(default_visibility = ["//visibility:public"])

pkg_tar(
    name = "darjeeling",
    testonly = True,
    srcs = [
        "//hw/ip/otp_ctrl/data:package",
        "//hw/top_darjeeling:package",
        "//hw/top_darjeeling/bitstream/vivado:package",
        "//sw/device/examples/hello_world:package",
        "//sw/device/lib/testing/test_rom:package",
        "//sw/device/silicon_creator/rom:package_fake",
        "//sw/device/silicon_creator/rom:package_real",
        "//sw/host/opentitantool:package",
    ],
    extension = "tar.xz",
    tags = ["manual"],
)

pkg_tar(
    name = "earlgrey",
    testonly = True,
    srcs = [
        "//hw/ip/otp_ctrl/data:package",
        "//hw/top_earlgrey:package",
        "//hw/top_earlgrey/bitstream/vivado:package",
        "//sw/device/examples/hello_world:package",
        "//sw/device/lib/testing/test_rom:package",
        "//sw/device/silicon_creator/rom:package_fake",
        "//sw/device/silicon_creator/rom:package_real",
        "//sw/host/opentitantool:package",
    ],
    extension = "tar.xz",
    tags = ["manual"],
)

release(
    name = "release",
    testonly = True,
    artifacts = {
        ":darjeeling": "Opentitan darjeeling software and FPGA artifacts",
        ":earlgrey": "Opentitan earlgrey software and FPGA artifacts",
    },
    tags = ["manual"],
)
