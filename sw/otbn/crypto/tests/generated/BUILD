# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_binary")
load("//rules:otbn.bzl", "otbn_autogen_sim_test", "otbn_sim_testgen")

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

# Run randomly generated tests for SHA3.
py_binary(
    name = "sha3_testgen",
    srcs = ["sha3_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
        requirement("pycryptodome"),
    ],
)

[
    otbn_autogen_sim_test(
        name = "sha3_test" + str(i),
        srcs = ["sha3_py_test.s"],
        seed = i,
        testgen = ":sha3_testgen",
        deps = [
            "//sw/otbn/crypto:sha3_shake",
        ],
    )
    for i in range(10)
]

# Run randomly generated tests for SHAKE.
py_binary(
    name = "shake_testgen",
    srcs = ["shake_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
        requirement("pycryptodome"),
    ],
)

[
    otbn_autogen_sim_test(
        name = "shake_test" + str(i),
        srcs = ["shake_py_test.s"],
        seed = i,
        testgen = ":shake_testgen",
        deps = [
            "//sw/otbn/crypto:sha3_shake",
        ],
    )
    for i in range(10)
]

py_binary(
    name = "mod_f4_testgen",
    srcs = ["mod_f4_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

otbn_sim_testgen(
    name = "mod_f4_test",
    srcs = [
        "mod_f4_test.s",
    ],
    number = 10,
    testgen = ":mod_f4_testgen",
    type = "testcase",
    deps = [
        "//sw/otbn/crypto:gcd",
    ],
)

py_binary(
    name = "div_word_testgen",
    srcs = ["div_word_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

otbn_sim_testgen(
    name = "div_word_test",
    srcs = [
        "div_word_test.s",
    ],
    number = 10,
    testgen = ":div_word_testgen",
    type = "testcase",
    deps = [
        "//sw/otbn/crypto:div",
    ],
)

py_binary(
    name = "modinv_f4_testgen",
    srcs = ["modinv_f4_testgen.py"],
    imports = [
        "../../../../../hw/ip/otbn/util",
    ],
    deps = [
        "//hw/ip/otbn/util/shared:testgen",
    ],
)

otbn_sim_testgen(
    name = "modinv_f4_test",
    srcs = [
        "modinv_f4_test.s",
    ],
    number = 10,
    testgen = ":modinv_f4_testgen",
    type = "testcase",
    deps = [
        "//sw/otbn/crypto:div",
        "//sw/otbn/crypto:gcd",
        "//sw/otbn/crypto:mul",
        "//sw/otbn/crypto:rsa_modinv_f4",
    ],
)
