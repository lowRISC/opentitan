# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_library")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "testutil",
    srcs = ["testutil.py"],
    deps = [
        requirement("py"),
        "//hw/ip/otbn/dv/otbnsim/sim",
        "//hw/ip/otbn/dv/otbnsim/sim:load_elf",
        "//hw/ip/otbn/dv/otbnsim/sim:standalonesim",
    ],
)

py_test(
    name = "simple_test",
    srcs = ["simple_test.py"],
    deps = [
        ":testutil",
        "//hw/ip/otbn/util/shared:reg_dump",
        "//hw/ip/otbn/util/shared:testgen",
        requirement("py"),
    ],
)

py_test(
    name = "state_test",
    srcs = ["state_test.py"],
    deps = [
        "//hw/ip/otbn/dv/otbnsim/sim",
        "//hw/ip/otbn/dv/otbnsim/sim:load_elf",
        "//hw/ip/otbn/dv/otbnsim/sim:standalonesim",
        requirement("py"),
    ],
)

py_test(
    name = "stats_test",
    srcs = ["stats_test.py"],
    deps = [
        "//hw/ip/otbn/dv/otbnsim/sim",
        "//hw/ip/otbn/dv/otbnsim/sim:load_elf",
        "//hw/ip/otbn/dv/otbnsim/sim:standalonesim",
        requirement("py"),
    ],
)
