# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

py_binary(
    name = "standalone",
    srcs = ["standalone.py"],
    deps = [
        "//hw/ip/otbn/dv/otbnsim/sim:load_elf",
        "//hw/ip/otbn/dv/otbnsim/sim:standalonesim",
        "//hw/ip/otbn/dv/otbnsim/sim:stats",
    ],
)

py_binary(
    name = "stepped",
    srcs = ["stepped.py"],
    deps = [
        "//hw/ip/otbn/dv/otbnsim/sim:load_elf",
    ],
)
