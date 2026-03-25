# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_autogen_sim_test", "otbn_library", "otbn_sim_test", "otbn_sim_test_suite", "otbn_sim_testgen")
load("@rules_python//python:defs.bzl", "py_binary")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

mldsa87_srcs = [
    "//sw/otbn/crypto/mldsa87:mldsa87_verify_ops.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_expand.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_sample.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_rounding.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_xof.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_norm.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_encoding.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_ntt.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_arith.s",
    "//sw/otbn/crypto/mldsa87:mldsa87_utils.s",
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
    "mldsa87_xof_shake128_test",
    "mldsa87_xof_shake256_test",
    "mldsa87_shift_left_test",
    "mldsa87_decompose_test",
    "mldsa87_check_infinity_norm_test",
    "mldsa87_rej_ntt_poly_test",
    "mldsa87_expand_a_test",
    "mldsa87_sample_in_ball_test",
    "mldsa87_challenge_hash_test",
    "mldsa87_decode_z_test",
    "mldsa87_decode_t1_test",
    "mldsa87_decode_h_test",
    "mldsa87_encode_w1_test",
    "mldsa87_sig_decode_test",
    "mldsa87_check_infinity_norm_z_test",
    "mldsa87_compute_w_approx_test",
    "mldsa87_use_hint_test",
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
        srcs = mldsa87_srcs + [
            # This is a top-level OTBN application test.
            # Make sure the memory file is placed after all the sources.
            "//sw/otbn/crypto/mldsa87:mldsa87_%s.s" % test.split("_")[1],
            "//sw/otbn/crypto/mldsa87:mldsa87_%s_mem.s" % test.split("_")[1],
            "mldsa87_%s_test.s" % test.split("_")[1],
        ],
        testcase = test + ".hjson",
    )
    for test in mldsa87_nist_tests
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
