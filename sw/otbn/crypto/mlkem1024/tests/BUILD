# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:otbn.bzl", "otbn_sim_test", "otbn_sim_testgen")
load("@rules_python//python:defs.bzl", "py_binary", "py_library")

package(default_visibility = ["//visibility:public"])

srcs = [
    "//sw/otbn/crypto:xof.s",
    "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
    "//sw/otbn/crypto/mlkem1024:mlkem1024_sample.s",
    "//sw/otbn/crypto/mlkem1024:mlkem1024_expand.s",
    "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
    "//sw/otbn/crypto/mlkem1024:mlkem1024_encoding.s",
    "//sw/otbn/crypto/mlkem1024:mlkem1024_decoding.s",
    "mlkem1024_test_mem.s",
]

unit_tests = [
    "mlkem1024_poly_add_test",
    "mlkem1024_poly_sub_test",
    "mlkem1024_poly_mul_test",
    "mlkem1024_poly_mul_add_test",
    "mlkem1024_basemul_test",
    "mlkem1024_sample_ntt_test",
    "mlkem1024_sample_cbd_test",
    "mlkem1024_expand_a_test",
    "mlkem1024_expand_prf_test",
    "mlkem1024_encode_12_test",
    "mlkem1024_encode_11_test",
    "mlkem1024_encode_5_test",
    "mlkem1024_encode_1_test",
    "mlkem1024_compress_11_test",
    "mlkem1024_compress_5_test",
    "mlkem1024_compress_1_test",
    "mlkem1024_decode_12_test",
    "mlkem1024_decode_11_test",
    "mlkem1024_decode_5_test",
    "mlkem1024_decode_1_test",
    "mlkem1024_decompress_11_test",
    "mlkem1024_decompress_5_test",
    "mlkem1024_ntt_test",
    "mlkem1024_intt_test",
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
    name = "mlkem1024_ntt_testgen",
    srcs = ["mlkem1024_ntt_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

py_binary(
    name = "mlkem1024_intt_testgen",
    srcs = ["mlkem1024_intt_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

py_binary(
    name = "mlkem1024_poly_mul_testgen",
    srcs = ["mlkem1024_poly_mul_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

py_binary(
    name = "mlkem1024_poly_mul_add_testgen",
    srcs = ["mlkem1024_poly_mul_add_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

otbn_sim_testgen(
    name = "mlkem1024_ntt_rand_test",
    srcs = [
        "mlkem1024_ntt_test.s",
        "mlkem1024_test_mem.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
    ],
    number = 10,
    testgen = ":mlkem1024_ntt_testgen",
    type = "testcase",
)

otbn_sim_testgen(
    name = "mlkem1024_intt_rand_test",
    srcs = [
        "mlkem1024_intt_test.s",
        "mlkem1024_test_mem.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
    ],
    number = 10,
    testgen = ":mlkem1024_intt_testgen",
    type = "testcase",
)

otbn_sim_testgen(
    name = "mlkem1024_poly_mul_rand_test",
    srcs = [
        "mlkem1024_poly_mul_test.s",
        "mlkem1024_test_mem.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
    ],
    number = 10,
    testgen = ":mlkem1024_poly_mul_testgen",
    type = "testcase",
)

otbn_sim_testgen(
    name = "mlkem1024_poly_mul_add_rand_test",
    srcs = [
        "mlkem1024_poly_mul_add_test.s",
        "mlkem1024_test_mem.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_arith.s",
        "//sw/otbn/crypto/mlkem1024:mlkem1024_ntt.s",
    ],
    number = 10,
    testgen = ":mlkem1024_poly_mul_add_testgen",
    type = "testcase",
)
