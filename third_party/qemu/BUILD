# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary", "py_library")
load("//rules:qemu.bzl", "qemu_build")

py_binary(
    name = "cfggen",
    srcs = ["@qemu_opentitan//:scripts/opentitan/cfggen.py"],
    deps = [
        ":ot",
        requirement("hjson"),
    ],
)

py_binary(
    name = "flashgen",
    srcs = ["@qemu_opentitan//:scripts/opentitan/flashgen.py"],
    deps = [
        ":ot",
        requirement("pyelftools"),
    ],
)

py_binary(
    name = "otptool",
    srcs = ["@qemu_opentitan//:scripts/opentitan/otptool.py"],
    deps = [":ot"],
)

py_library(
    name = "ot",
    srcs = ["@qemu_opentitan//:ot"],
)

qemu_build(
    name = "qemu-system-riscv32",
    qemu_src = "@qemu_opentitan//:qemu_src",
)
