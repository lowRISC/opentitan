# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(["top_${topname}_flash_ctrl.ipconfig.hjson"])

filegroup(
    name = "doc_files",
    srcs = glob([
        "flash_ctrl.hjson",
        "*_testplan.hjson",
    ]),
)
