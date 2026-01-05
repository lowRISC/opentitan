# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _skywater_repos():
    http_archive(
        name = "sky130_fd_sc_hd",
        build_file_content = """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "libs",
    srcs = glob([
        "timing/*.lib",
        "timing/*.lib.gz",
    ], allow_empty = True),
)

filegroup(
    name = "verilog",
    srcs = glob([
        "cells/*/*.v",
    ], allow_empty = True),
)
""",
        urls = ["https://github.com/efabless/skywater-pdk-libs-sky130_fd_sc_hd/archive/master.zip"],
        strip_prefix = "skywater-pdk-libs-sky130_fd_sc_hd-master",
        integrity = "sha256-nEHzRoeQE6U2JF+13d8+Asw2C0NxJF2Rf+RIQIYD4Y4=",
    )

skywater = module_extension(
    implementation = lambda _: _skywater_repos(),
)
