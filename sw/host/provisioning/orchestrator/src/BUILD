# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary", "py_library")

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

py_library(
    name = "ot_dut",
    srcs = ["ot_dut.py"],
    imports = ["."],
    deps = [
        ":device_id",
        ":sku_config",
        ":util",
    ],
)

py_binary(
    name = "orchestrator",
    testonly = True,
    srcs = ["orchestrator.py"],
    data = [
        "//hw/bitstream/universal:splice",
        "//sw/device/silicon_creator/manuf/base:ft_personalize_all",
        "//sw/device/silicon_creator/manuf/base:sram_cp_provision",
        "//sw/device/silicon_creator/manuf/base:sram_ft_individualize_all",
        "//sw/device/silicon_creator/manuf/keys/fake:dice_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:sk.pkcs8.der",
        "//sw/host/provisioning/cp",
        "//sw/host/provisioning/ft:ft_all",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:jtag_olimex_cfg",
        "//third_party/openocd:openocd_bin",
    ],
    imports = ["."],
    deps = [
        ":device_id",
        ":ot_dut",
        ":sku_config",
        ":util",
        requirement("hjson"),
    ],
)
