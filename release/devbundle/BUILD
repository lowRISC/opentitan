# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_pkg//pkg:mappings.bzl", "pkg_filegroup", "pkg_files")
load("@rules_pkg//pkg:tar.bzl", "pkg_tar")
load("//rules:flags.bzl", "build_with_flags")
load("//rules/opentitan:splice.bzl", "bitstream_splice")

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
    prefix = "earlgrey/bitstreams",
    tags = ["manual"],
)

# Build up a cryptolib package with a conventional 'include/lib/*.h` and `lib/*.a` structure
pkg_files(
    name = "cryptolib_headers_pkg",
    srcs = [
        "//sw/device/lib/crypto/include:package",
    ],
    prefix = "include/libotcrypto",
)

pkg_files(
    name = "cryptolib_freestanding_headers_pkg",
    srcs = [
        "//sw/device/lib/crypto/include/freestanding:package",
    ],
    prefix = "include/libotcrypto/freestanding",
)

pkg_files(
    name = "cryptolib_archive_pkg",
    srcs = [
        "//sw/device/lib/crypto:package",
    ],
    prefix = "lib",
)

pkg_filegroup(
    name = "cryptolib_pkg",
    srcs = [
        ":cryptolib_archive_pkg",
        ":cryptolib_freestanding_headers_pkg",
        ":cryptolib_headers_pkg",
    ],
    prefix = "libotcrypto",
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

build_with_flags(
    name = "opentitantool",
    flags = {
        "//rules:static_link_host_tools": "True",
    },
    target = "//sw/host/opentitantool:package",
)

# TODO(cfrantz): Implement release automation so we don't have to publish the artifact manually.
# Upload this to the GCS bucket `artifacts.opentitan.org` and name the file
# with a date tag (e.g. devbundle-YYYYMMDD.tar.xz).
#
# For example:
# $ gcloud --account=foo@opentitan.org \
#       storage cp \
#           bazel-bin/release/devbundle/devbundle.tar.xz \
#           gs://artifacts.opentitan.org/dev_bundle/devbundle-20250718.tar.xz
pkg_tar(
    name = "devbundle",
    testonly = True,
    srcs = [
        ":bazel",
        ":bitstreams_pkg",
        ":cryptolib_pkg",
        ":opentitantool",
        "//hw:package",
        "//hw/ip/otp_ctrl/data:package",
        "//sw/device/lib/testing/test_rom:package",
        "//sw/device/silicon_creator/lib/ownership/keys/fake:fpga_dev_pkg",
        "//sw/device/silicon_creator/rom_ext:fpga_dev_pkg",
        # Note: a static build of hsmtool doesn't work because the PKCS#11
        # middleware libraries are typically dynamically linked and load
        # glibc and friends.
        "//sw/host/hsmtool:package",
        # Credits
        ":opentitan_credits",
        ":ibex_credits",
        ":rust_openssl_credits",
    ],
    extension = "tar.xz",
    tags = ["manual"],
)

pkg_files(
    name = "opentitan_credits",
    srcs = [
        # OpenTitan's Apache-2.0 license and NOTICE files:
        "//:LICENSE",
        "//:NOTICE",
    ],
    prefix = "CREDITS/opentitan/",
)

pkg_files(
    name = "ibex_credits",
    srcs = [
        # Ibex's Apache-2.0 license, NOTICE file, and CREDITS.md file.
        "//hw:vendor/lowrisc_ibex/LICENSE",
        "//hw:vendor/lowrisc_ibex/NOTICE",
        "//hw:vendor/lowrisc_ibex/CREDITS.md",
    ],
    prefix = "CREDITS/ibex/",
)

pkg_files(
    name = "rust_openssl_credits",
    srcs = [
        # OpenSSL is included in OpenTitanLib, we must distribute this file:
        "@rust_openssl//:THIRD_PARTY",
    ],
    prefix = "CREDITS/rust_openssl/",
)
