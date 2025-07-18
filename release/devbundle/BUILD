# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules/opentitan:splice.bzl", "bitstream_splice")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")

package(default_visibility = ["//visibility:public"])

bitstream_splice(
    name = "bitstream_fpga_hyper310",
    testonly = True,
    # When the src bitstream and mmi fields are empty, the rule will use values
    # from the exec_env.
    exec_env = "//hw/top_earlgrey:fpga_hyper310_rom_ext",
    otp = "//hw/bitstream/universal:none",
    rom = "//hw/bitstream/universal:none",
    tags = ["manual"],
)

bitstream_splice(
    name = "bitstream_fpga_hyper340",
    testonly = True,
    # When the src bitstream and mmi fields are empty, the rule will use values
    # from the exec_env.
    exec_env = "//hw/top_earlgrey:fpga_cw340_rom_ext",
    otp = "//hw/bitstream/universal:none",
    rom = "//hw/bitstream/universal:none",
    tags = ["manual"],
)

pkg_files(
    name = "bitstreams",
    testonly = True,
    srcs = [
        ":bitstream_fpga_hyper310",
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
    prefix = "bitstreams",
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

# TODO(cfrantz): Implement release automation so we don't have to publish the artifact manually.
# Upload this to the GCS bucket `artifacts.opentitan.org` and name the file
# with a date tag (e.g. devbundle-YYYYMMDD.tar.xz).
#
# For example:
# $ gcloud --acount=foo@opentitan.org \
#       storage cp \
#           bazel-bin/release/devbundle/devbundle.tar.xz \
#           gs://artifacts.opentitan.org/dev_bundle/devbundle-20250718.tar.xz
pkg_tar(
    name = "devbundle",
    testonly = True,
    srcs = [
        ":bazel",
        ":bitstreams_pkg",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:fpga_dev_pkg",
        "//sw/device/silicon_creator/rom_ext:fpga_dev_pkg",
        "//sw/host/opentitantool:package",
    ],
    extension = "tar.xz",
    tags = ["manual"],
)
