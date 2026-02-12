# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_binary(
    name = "sca_ibex_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_ibex_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_ibex_commands",
        "//sw/host/penetrationtests/python/sca:sca_ibex_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_aes_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_aes_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_aes_commands",
        "//sw/host/penetrationtests/python/sca:sca_aes_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_hmac_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_hmac_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_hmac_commands",
        "//sw/host/penetrationtests/python/sca:sca_hmac_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_kmac_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_kmac_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_kmac_commands",
        "//sw/host/penetrationtests/python/sca:sca_kmac_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_otbn_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_otbn_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_otbn_commands",
        "//sw/host/penetrationtests/python/sca:sca_otbn_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_sha3_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_sha3_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_sha3_commands",
        "//sw/host/penetrationtests/python/sca:sca_sha3_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_sym_cryptolib_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_sym_cryptolib_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_sym_cryptolib_commands",
        "//sw/host/penetrationtests/python/sca:sca_sym_cryptolib_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "sca_asym_cryptolib_python_test",
    testonly = True,
    srcs = ["test_scripts/sca_asym_cryptolib_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/sca:sca_asym_cryptolib_commands",
        "//sw/host/penetrationtests/python/sca:sca_asym_cryptolib_functions",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "sca_ibex_functions",
    srcs = ["host_scripts/sca_ibex_functions.py"],
    deps = [
        ":sca_ibex_commands",
        ":sca_prng_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_aes_functions",
    srcs = ["host_scripts/sca_aes_functions.py"],
    deps = [
        ":sca_aes_commands",
        ":sca_prng_commands",
        ":sca_trigger_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_hmac_functions",
    srcs = ["host_scripts/sca_hmac_functions.py"],
    deps = [
        ":sca_hmac_commands",
        ":sca_prng_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_kmac_functions",
    srcs = ["host_scripts/sca_kmac_functions.py"],
    deps = [
        ":sca_kmac_commands",
        ":sca_prng_commands",
        ":sca_trigger_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_otbn_functions",
    srcs = ["host_scripts/sca_otbn_functions.py"],
    deps = [
        ":sca_otbn_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_sha3_functions",
    srcs = ["host_scripts/sca_sha3_functions.py"],
    deps = [
        ":sca_prng_commands",
        ":sca_sha3_commands",
        ":sca_trigger_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_sym_cryptolib_functions",
    srcs = ["host_scripts/sca_sym_cryptolib_functions.py"],
    deps = [
        ":sca_prng_commands",
        ":sca_sym_cryptolib_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_asym_cryptolib_functions",
    srcs = ["host_scripts/sca_asym_cryptolib_functions.py"],
    deps = [
        ":sca_asym_cryptolib_commands",
        ":sca_prng_commands",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "sca_ibex_commands",
    srcs = ["communication/sca_ibex_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_aes_commands",
    srcs = ["communication/sca_aes_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_hmac_commands",
    srcs = ["communication/sca_hmac_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_kmac_commands",
    srcs = ["communication/sca_kmac_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_otbn_commands",
    srcs = ["communication/sca_otbn_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_prng_commands",
    srcs = ["communication/sca_prng_commands.py"],
)

py_library(
    name = "sca_sha3_commands",
    srcs = ["communication/sca_sha3_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_sym_cryptolib_commands",
    srcs = ["communication/sca_sym_cryptolib_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_asym_cryptolib_commands",
    srcs = ["communication/sca_asym_cryptolib_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "sca_trigger_commands",
    srcs = ["communication/sca_trigger_commands.py"],
)
