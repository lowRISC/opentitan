# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

exports_files(["top_${topname}_${module_instance_name}.ipconfig.hjson"])

filegroup(
    name = "doc_files",
    srcs = ["${module_instance_name}.hjson"],
)
