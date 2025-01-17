# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "EARLGREY_SKUS",
)

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

filegroup(
    name = "all",
    srcs = depset([
        config["orchestrator_cfg"]
        for _, config in EARLGREY_SKUS.items()
    ]).to_list(),
)
