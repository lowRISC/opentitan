# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "doc_files",
    srcs = glob(["**/*.md"]) + [
        "//hw/dv/sv:doc_files",
        "//hw/dv/tools/dvsim/testplans:doc_files",
    ],
)

filegroup(
    name = "verilator_files",
    srcs = glob(["verilator/**"]),
    visibility = ["//visibility:public"],
)

filegroup(
    name = "dpi_files",
    srcs = glob(["dpi/**"]),
    visibility = ["//visibility:public"],
)
