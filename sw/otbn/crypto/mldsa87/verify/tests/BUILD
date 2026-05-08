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
    "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify_encoding.s",
    "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify_norm.s",
    "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify_rounding.s",
    "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify_ops.s",
]

unit_tests = [
    "mldsa87_verify_decode_z_test",
    "mldsa87_verify_decode_t1_test",
    "mldsa87_verify_decode_h_test",
    "mldsa87_verify_check_infinity_norm_test",
    "mldsa87_verify_decompose_test",
    "mldsa87_verify_shift_left_test",
    "mldsa87_verify_decode_sig_test",
    "mldsa87_verify_check_infinity_norm_z_test",
    "mldsa87_verify_compute_w_approx_test",
    "mldsa87_verify_use_hint_test",
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

mldsa87_nist_tests = [
    "mldsa87_verify_nist_acvp_63_test",
    "mldsa87_verify_nist_acvp_65_test",
    "mldsa87_verify_nist_acvp_66_test",
    "mldsa87_verify_nist_acvp_68_test",
    "mldsa87_verify_nist_acvp_69_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = srcs + [
            # This is a top-level OTBN application test.
            # Make sure the memory file is placed after all the sources.
            "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify.s",
            "//sw/otbn/crypto/mldsa87/verify:mldsa87_verify_mem.s",
            "mldsa87_verify_test.s",
        ],
        testcase = test + ".hjson",
    )
    for test in mldsa87_nist_tests
]
