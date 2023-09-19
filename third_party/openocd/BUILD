# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:private"])

load("@rules_foreign_cc//foreign_cc:configure.bzl", "configure_make")

# Extract the `openocd` binary from :build_openocd. Although the binary itself
# is executable, Bazel does not believe it is runnable. If you want to run
# OpenOCD, use the runnable wrapper like so: `bazel run //third_party/openocd`.
filegroup(
    name = "openocd_bin",
    srcs = [":build_openocd"],
    output_group = "openocd",
    visibility = ["//visibility:public"],
)

genrule(
    name = "openocd",
    outs = ["openocd.sh"],
    cmd = """
    echo '#!/bin/bash' > $@
    echo './$(execpath :openocd_bin) "$$@"' >> $@
    """,
    executable = True,
    tools = [":openocd_bin"],
    visibility = ["//visibility:public"],
)

filegroup(
    name = "jtag_ftdi_cfg",
    srcs = ["//util/openocd/board:cw340_ftdi.cfg"],
    visibility = ["//visibility:public"],
)

filegroup(
    name = "jtag_olimex_cfg",
    srcs = ["@openocd//:tcl/interface/ftdi/olimex-arm-usb-tiny-h.cfg"],
    visibility = ["//visibility:public"],
)

configure_make(
    name = "build_openocd",
    # Speed up the build with multiple jobs, but set an upper bound to constrain
    # memory consumption. Bazel is not aware of foreign builds' resource usage.
    # See <https://github.com/bazelbuild/rules_foreign_cc/issues/329>.
    args = [
        "-j",
        "`nproc`",
    ],
    configure_in_place = True,
    configure_options = [
        "--enable-ftdi",
        "--enable-verbose-jtag-io",
        "--disable-vsllink",
        "--enable-remote-bitbang",
    ],
    copts = ["-Wno-error=unused-variable"],
    env = {"CCACHE": "none"},
    lib_source = "@openocd//:all_srcs",
    out_binaries = ["openocd"],
)
