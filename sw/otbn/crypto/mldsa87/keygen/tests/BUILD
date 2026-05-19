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
    "//sw/otbn/crypto/mldsa87/keygen:mldsa87_keygen_sample.s",
    "//sw/otbn/crypto/mldsa87/keygen:mldsa87_keygen_expand.s",
    "//sw/otbn/crypto/mldsa87/keygen:mldsa87_keygen_encoding.s",
    "//sw/otbn/crypto/mldsa87/keygen:mldsa87_keygen_rounding.s",
]

unit_tests = [
    "mldsa87_keygen_rej_bounded_poly_test",
    "mldsa87_keygen_expand_s1_test",
    "mldsa87_keygen_expand_s2_test",
    "mldsa87_keygen_encode_t0_test",
    "mldsa87_keygen_encode_t1_test",
    "mldsa87_keygen_power2round_test",
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
