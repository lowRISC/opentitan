# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_sim_test", "otbn_sim_testgen")
load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

srcs = [
    "//sw/otbn/crypto/mldsa87:mldsa87_utils.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_arith.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_sample.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_encoding.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_gadgets.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_xof.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_expand.s",
]

unit_tests = [
    "mldsa87_poly_add_test",
    "mldsa87_poly_sub_test",
    "mldsa87_poly_mul_test",
    "mldsa87_poly_mul_add_test",
    "mldsa87_ntt_test",
    "mldsa87_intt_test",
    "mldsa87_ntt_intt_test",
    "mldsa87_rej_ntt_poly_test",
    "mldsa87_sample_in_ball_test",
    "mldsa87_challenge_hash_test",
    "mldsa87_expand_a_test",
    "mldsa87_encode_w1_test",
    "mldsa87_xof_shake128_test",
    "mldsa87_xof_shake256_test",
    "mldsa87_sec_a2b_test",
    "mldsa87_sec_b2a_test",
    "mldsa87_sec_add_test",
    "mldsa87_sec_unmask_test",
    "mldsa87_sec_leq_test",
    "mldsa87_sec_bound_check_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = srcs + [
            test + ".s",
        ],
        testcase = test + ".hjson",
    )
    for test in unit_tests
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
