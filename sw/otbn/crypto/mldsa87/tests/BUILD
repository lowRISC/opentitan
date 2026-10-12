# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_sim_test", "otbn_sim_testgen")
load("@rules_python//python:defs.bzl", "py_binary")

package(default_visibility = ["//visibility:public"])

#####################
# Common unit tests #
#####################

COMMON_TESTS = [
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
    "mldsa87_decode_s_test",
    "mldsa87_sec_bound_check_test",
    "mldsa87_sec_decompose_test",
    "mldsa87_sec_mod5_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = [test + ".s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87:mldsa87_routines"],
    )
    for test in COMMON_TESTS
]

#####################
# Keygen unit tests #
#####################

KEYGEN_TESTS = [
    "mldsa87_keygen_rej_bounded_poly_test",
    "mldsa87_keygen_expand_s1_test",
    "mldsa87_keygen_expand_s2_test",
    "mldsa87_keygen_encode_t0_test",
    "mldsa87_keygen_encode_t1_test",
    "mldsa87_keygen_power2round_test",
    "mldsa87_keygen_encode_s_test",
    "mldsa87_keygen_sample_s_test",
    "mldsa87_keygen_compute_t_test",
    "mldsa87_keygen_encode_t_test",
    "mldsa87_keygen_hash_seed_test",
    "mldsa87_keygen_hash_pk_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = [test + ".s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87:mldsa87_routines"],
    )
    for test in KEYGEN_TESTS
]

###################
# Sign unit tests #
###################

SIGN_TESTS = [
    "mldsa87_sign_sample_mask_poly_test",
    "mldsa87_sign_expand_mask_test",
    "mldsa87_sign_decode_t0_test",
    "mldsa87_sign_decode_w1_test",
    "mldsa87_sign_encode_z_test",
    "mldsa87_sign_compute_w_test",
    "mldsa87_sign_decompose_w_test",
    "mldsa87_sign_compute_z_test",
    "mldsa87_sign_compute_r0_pos_test",
    "mldsa87_sign_compute_r0_neg_test",
    "mldsa87_sign_compute_x0_test",
    "mldsa87_sign_make_hint_test",
    "mldsa87_sign_hw_check_hint_test",
    "mldsa87_sign_compress_hint_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = [test + ".s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87:mldsa87_routines"],
    )
    for test in SIGN_TESTS
]

#####################
# Verify unit tests #
#####################

VERIFY_TESTS = [
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
    "mldsa87_verify_check_hint_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = [test + ".s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87:mldsa87_routines"],
    )
    for test in VERIFY_TESTS
]

###################
# NIST ACVP tests #
###################

KEYGEN_NIST_TESTS = [
    "mldsa87_keygen_nist_acvp_51_test",
    "mldsa87_keygen_nist_acvp_52_test",
    "mldsa87_keygen_nist_acvp_53_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = ["mldsa87_keygen_test.s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87"],
    )
    for test in KEYGEN_NIST_TESTS
]

SIGN_NIST_TESTS = [
    "mldsa87_sign_nist_acvp_61_test",
    "mldsa87_sign_nist_acvp_62_test",
    "mldsa87_sign_nist_acvp_74_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = ["mldsa87_sign_test.s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87"],
    )
    for test in SIGN_NIST_TESTS
]

VERIFY_NIST_TESTS = [
    "mldsa87_verify_nist_acvp_63_test",
    "mldsa87_verify_nist_acvp_64_test",
    "mldsa87_verify_nist_acvp_65_test",
    "mldsa87_verify_nist_acvp_66_test",
    "mldsa87_verify_nist_acvp_68_test",
    "mldsa87_verify_nist_acvp_69_test",
]

[
    otbn_sim_test(
        name = test,
        srcs = ["mldsa87_verify_test.s"],
        includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
        testcase = test + ".hjson",
        deps = ["//sw/otbn/crypto/mldsa87"],
    )
    for test in VERIFY_NIST_TESTS
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
    srcs = ["mldsa87_ntt_test.s"],
    includes = ["//sw/otbn/crypto/mldsa87:mldsa87.inc"],
    number = 10,
    testgen = ":mldsa87_ntt_testgen",
    type = "testcase",
    deps = ["//sw/otbn/crypto/mldsa87:mldsa87_routines"],
)
