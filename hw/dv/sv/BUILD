# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "dv_common_files",
    srcs = glob(["**"]),
)

filegroup(
    name = "dv_macros",
    srcs = glob(["dv_utils/**"]),
)

filegroup(
    name = "doc_files",
    srcs = glob([
        "**/*.md",
        "**/*.svg",
    ]) + [
        "//hw/dv/sv/alert_esc_agent/data:doc_files",
        "//hw/dv/sv/mem_bkdr_scb/data:doc_files",
    ],
)
