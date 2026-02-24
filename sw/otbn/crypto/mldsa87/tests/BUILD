# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_autogen_sim_test", "otbn_library", "otbn_sim_test", "otbn_sim_test_suite", "otbn_sim_testgen")
load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

mldsa87_srcs = [
    "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_arith.s",
]

# Naming convention for the unit tests: Test, *.s and *.hjson files
# have the same name.
mldsa87_unit_tests = [
    "mldsa87_ntt_test",
    "mldsa87_intt_test",
    "mldsa87_ntt_intt_test",
    "mldsa87_poly_mul_test",
    "mldsa87_poly_add_test",
    "mldsa87_poly_sub_test",
    "mldsa87_poly_mul_add_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = mldsa87_srcs + [
            test + ".s",
        ],
        testcase = test + ".hjson",
    )
    for test in mldsa87_unit_tests
]

####################
# Randomized tests #
####################

py_binary(
    name = "mldsa87_ntt_testgen",
    srcs = ["mldsa87_ntt_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

otbn_sim_testgen(
    name = "mldsa87_ntt_rand_test",
    srcs = [
        "mldsa87_ntt_test.s",
        "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
    ],
    number = 10,
    testgen = ":mldsa87_ntt_testgen",
    type = "testcase",
)
