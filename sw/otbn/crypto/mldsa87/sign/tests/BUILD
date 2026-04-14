# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_sim_test")

package(default_visibility = ["//visibility:public"])

srcs = [
    "//sw/otbn/crypto/mldsa87:mldsa87_utils.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_arith.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_sample.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_encoding.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_xof.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_expand.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_gadgets.s",
    "//sw/otbn/crypto/mldsa87/sign:mldsa87_sign_sample.s",
]

unit_tests = [
    "mldsa87_sign_sample_mask_poly_test",
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
