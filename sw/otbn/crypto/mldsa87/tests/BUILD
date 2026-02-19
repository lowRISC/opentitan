# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_library", "otbn_sim_test", "otbn_sim_test_suite")

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
