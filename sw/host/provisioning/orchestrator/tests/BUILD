# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_test")

package(default_visibility = ["//visibility:public"])

py_test(
    name = "device_id_test",
    srcs = ["device_id_test.py"],
    data = [
        "//sw/device/silicon_creator/manuf/keys/fake:dice_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:sk.pkcs8.der",
        "//sw/host/provisioning/orchestrator/configs/skus:sival.hjson",
    ],
    deps = [
        requirement("hjson"),
        "//sw/host/provisioning/orchestrator/src:device_id",
        "//sw/host/provisioning/orchestrator/src:sku_config",
        "//sw/host/provisioning/orchestrator/src:util",
    ],
)
