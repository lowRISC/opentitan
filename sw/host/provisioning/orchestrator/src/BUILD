# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_library")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "device_id",
    srcs = ["device_id.py"],
    data = [
        "//sw/host/provisioning/orchestrator/data:products.hjson",
        "//sw/host/provisioning/orchestrator/data/packages:earlgrey_a1.hjson",
    ],
    imports = ["."],
    deps = [
        ":sku_config",
        ":util",
        requirement("hjson"),
    ],
)

py_library(
    name = "ca_config",
    srcs = ["ca_config.py"],
)

py_library(
    name = "sku_config",
    srcs = ["sku_config.py"],
    data = [
        "//sw/host/provisioning/orchestrator/data:products.hjson",
        "//sw/host/provisioning/orchestrator/data/packages:earlgrey_a1.hjson",
    ],
    deps = [
        ":ca_config",
        ":util",
        requirement("hjson"),
    ],
)

py_library(
    name = "util",
    srcs = ["util.py"],
    imports = ["."],
    deps = [requirement("hjson")],
)
