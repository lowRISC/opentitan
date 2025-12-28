# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_tools//tools/build_defs/repo:http.bzl", "http_archive")

def _yosys_repos():
    http_archive(
        name = "yosys",
        build_file_content = """
package(default_visibility = ["//visibility:public"])

filegroup(
    name = "yosys_bin",
    srcs = ["bin/yosys"],
)

filegroup(
    name = "data",
    srcs = glob([
        "share/**", 
        "lib/**", 
        "libexec/**",
        "bin/**",
    ]),
)
""",
        urls = ["https://github.com/YosysHQ/oss-cad-suite-build/releases/download/2024-01-01/oss-cad-suite-linux-x64-20240101.tgz"],
        strip_prefix = "oss-cad-suite",
        integrity = "sha256-SPOrxaZ/pJrbSMhyf3t9BCOg78hpmmErO3vJFv9TQC8=",
    )

yosys = module_extension(
    implementation = lambda _: _yosys_repos(),
)
