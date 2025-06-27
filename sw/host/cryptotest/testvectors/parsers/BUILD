# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@rules_python//python:defs.bzl", "py_binary", "py_library", "py_test")
load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_library(
    name = "cryptotest_util",
    srcs = ["cryptotest_util.py"],
    visibility = ["//visibility:private"],
)

py_test(
    name = "cryptotest_util_test",
    srcs = [
        "cryptotest_util.py",
        "cryptotest_util_test.py",
    ],
    visibility = ["//visibility:private"],
)

py_binary(
    name = "nist_aes_parser",
    srcs = ["nist_aes_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_aes_gcm_parser",
    srcs = ["nist_cavp_aes_gcm_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_drbg_parser",
    srcs = ["nist_cavp_drbg_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_ecdsa_parser",
    srcs = ["nist_cavp_ecdsa_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_aes_kw_parser",
    srcs = ["nist_cavp_aes_kw_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "wycheproof_ecdsa_parser",
    srcs = ["wycheproof_ecdsa_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "hjson_hash_parser",
    srcs = ["hjson_hash_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("hjson"),
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "random_ecdsa_generator",
    srcs = ["random_ecdsa_generator.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "nist_cavp_hash_parser",
    srcs = ["nist_cavp_hash_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_hmac_parser",
    srcs = ["nist_cavp_hmac_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "wycheproof_hmac_parser",
    srcs = ["wycheproof_hmac_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_ecdh_parser",
    srcs = ["nist_cavp_ecdh_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "wycheproof_ecdh_parser",
    srcs = ["wycheproof_ecdh_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "hjson_kmac_parser",
    srcs = ["hjson_kmac_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("hjson"),
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "wycheproof_kmac_parser",
    srcs = ["wycheproof_kmac_parser.py"],
    deps = [
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "nist_cavp_rsa_parser",
    srcs = ["nist_cavp_rsa_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "rsp_sphincsplus_parser",
    srcs = ["rsp_sphincsplus_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "wycheproof_ed25519_parser",
    srcs = ["wycheproof_ed25519_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "wycheproof_rsa_parser",
    srcs = ["wycheproof_rsa_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("jsonschema"),
    ],
)

py_binary(
    name = "hjson_rsa_parser",
    srcs = ["hjson_rsa_parser.py"],
    deps = [
        ":cryptotest_util",
        requirement("hjson"),
        requirement("jsonschema"),
    ],
)
