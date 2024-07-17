# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary")
load("//rules:otbn.bzl", "otbn_autogen_sim_test")

package(default_visibility = ["//visibility:public"])

py_binary(
    name = "mul_testgen",
    srcs = ["mul_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

# Run randomly generated tests. Note that the random test data will be the same
# for the same seed every time, because Bazel always builds "hermetically" and
# therefore cannot generate any actually random values at build time.
[
    otbn_autogen_sim_test(
        name = "mul_test" + str(i),
        srcs = ["mul_test.s"],
        seed = i,
        testgen = ":mul_testgen",
        deps = [
            "//sw/otbn/crypto:mul",
        ],
    )
    for i in range(10)
]
