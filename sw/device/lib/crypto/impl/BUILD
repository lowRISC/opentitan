# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

load("//rules/opentitan:defs.bzl", "OPENTITAN_CPU")
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_TEST_ENVS",
    "cw310_params",
    "fpga_params",
    "opentitan_test",
    "verilator_params",
)

config_setting(
    name = "crypto_status_debug",
    define_values = {
        "crypto_status_debug": "true",
    },
)

config_setting(
    name = "release_build",
    define_values = {
        "release_build": "true",
    },
)

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["//sw/device/lib/crypto/include:aes.h"],
    deps = [
        ":config",
        ":integrity",
        ":keyblob",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:aes",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "aes_gcm",
    srcs = ["aes_gcm.c"],
    hdrs = ["//sw/device/lib/crypto/include:aes_gcm.h"],
    deps = [
        ":config",
        ":integrity",
        ":keyblob",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/crypto/drivers:aes",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl/aes_gcm",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "cryptolib_build_info",
    srcs = ["cryptolib_build_info.c"],
    hdrs = ["//sw/device/lib/crypto/include:cryptolib_build_info.h"],
    defines = select({
        ":release_build": ["CRYPTOLIB_IS_RELEASED=true"],
        "//conditions:default": ["CRYPTOLIB_IS_RELEASED=false"],
    }),
    deps = [
        ":status",
        "//sw/device/lib/crypto/drivers:cryptolib_build_info",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "drbg",
    srcs = ["drbg.c"],
    hdrs = ["//sw/device/lib/crypto/include:drbg.h"],
    deps = [
        ":config",
        ":integrity",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:math",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "ecc_curve25519",
    srcs = ["ecc_curve25519.c"],
    hdrs = ["//sw/device/lib/crypto/include:ecc_curve25519.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":config",
        ":hmac",
        ":integrity",
        ":keyblob",
        ":sha2",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/impl/ecc:curve25519",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "ecc_p256",
    srcs = ["ecc_p256.c"],
    hdrs = ["//sw/device/lib/crypto/include:ecc_p256.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":config",
        ":keyblob",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/impl/ecc:p256",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "ecc_p384",
    srcs = ["ecc_p384.c"],
    hdrs = ["//sw/device/lib/crypto/include:ecc_p384.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":config",
        ":keyblob",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/impl/ecc:p384",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "hkdf",
    srcs = ["hkdf.c"],
    hdrs = ["//sw/device/lib/crypto/include:hkdf.h"],
    deps = [
        ":config",
        ":hmac",
        ":integrity",
        ":keyblob",
        ":status",
        "//sw/device/lib/base:math",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "integrity",
    srcs = ["integrity.c"],
    hdrs = ["//sw/device/lib/crypto/include:integrity.h"],
    deps = [
        "//sw/device/lib/base:crc32_device_library",  # force non-mock version in unit tests
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "integrity_unittest",
    srcs = ["integrity_unittest.cc"],
    deps = [
        ":integrity",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "kats",
    srcs = ["kats.c"],
    hdrs = ["kats.h"],
    deps = [
        ":aes",
        ":aes_gcm",
        ":config",
        ":drbg",
        ":ecc_p256",
        ":ecc_p384",
        ":entropy_src",
        ":hmac",
        ":integrity",
        ":keyblob",
        ":kmac",
        ":rsa",
        ":sha2",
        ":sha3",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:entropy_kat",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "kdf_ctr",
    srcs = ["kdf_ctr.c"],
    hdrs = ["//sw/device/lib/crypto/include:kdf_ctr.h"],
    deps = [
        ":config",
        ":hmac",
        ":integrity",
        ":keyblob",
        ":status",
        "//sw/device/lib/base:math",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "keyblob",
    srcs = ["keyblob.c"],
    hdrs = ["keyblob.h"],
    deps = [
        ":integrity",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:math",
        "//sw/device/lib/crypto/drivers:keymgr",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "keyblob_unittest",
    srcs = ["keyblob_unittest.cc"],
    deps = [
        ":keyblob",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "key_transport",
    srcs = ["key_transport.c"],
    hdrs = ["//sw/device/lib/crypto/include:key_transport.h"],
    deps = [
        ":config",
        ":status",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl:drbg",
        "//sw/device/lib/crypto/impl:integrity",
        "//sw/device/lib/crypto/impl:keyblob",
        "//sw/device/lib/crypto/impl/aes_kwp",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "key_transport_unittest",
    srcs = ["key_transport_unittest.cc"],
    deps = [
        ":key_transport",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "kmac_kdf",
    srcs = ["kmac_kdf.c"],
    hdrs = ["//sw/device/lib/crypto/include:kmac_kdf.h"],
    deps = [
        ":config",
        ":integrity",
        ":keyblob",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:math",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "rsa",
    srcs = ["rsa.c"],
    hdrs = ["//sw/device/lib/crypto/include:rsa.h"],
    deps = [
        ":config",
        ":integrity",
        ":status",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/impl/rsa:rsa_encryption",
        "//sw/device/lib/crypto/impl/rsa:rsa_signature",
        "//sw/device/lib/crypto/impl/rsa:run_rsa_key_from_cofactor",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "config",
    srcs = ["config.c"],
    hdrs = ["//sw/device/lib/crypto/include:config.h"],
    deps = [
        ":entropy_src",
        ":integrity",
        ":status",
        "//hw/top_earlgrey/ip_autogen/clkmgr:clkmgr_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:abs_mmio",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:alert",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
    ],
)

cc_library(
    name = "sha2",
    srcs = ["sha2.c"],
    hdrs = [
        "//sw/device/lib/crypto/include:sha2.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":config",
        ":integrity",
        ":status",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "sha3",
    srcs = ["sha3.c"],
    hdrs = [
        "//sw/device/lib/crypto/include:sha3.h",
    ],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":config",
        ":status",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "status",
    hdrs = [
        "status.h",
    ],
    # Turn debugging on only if the `crypto_status_debug` command-line option
    # is set.
    defines = select({
        ":crypto_status_debug": ["OTCRYPTO_STATUS_DEBUG"],
        "//conditions:default": [],
    }),
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_test(
    name = "status_unittest",
    srcs = ["status_unittest.cc"],
    deps = [
        ":status",
        "@googletest//:gtest_main",
    ],
)

# Status-code unit tests with debugging information always on.
cc_test(
    name = "status_debug_unittest",
    srcs = ["status_debug_unittest.cc"],
    defines = ["OTCRYPTO_STATUS_DEBUG"],
    deps = [
        ":status",
        "@googletest//:gtest_main",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = [
        "//sw/device/lib/crypto/include:hmac.h",
    ],
    deps = [
        ":config",
        ":integrity",
        ":keyblob",
        ":sha2",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:hmac",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
    ],
)

cc_library(
    name = "kmac",
    srcs = ["kmac.c"],
    hdrs = [
        "//sw/device/lib/crypto/include:kmac.h",
    ],
    deps = [
        ":config",
        ":integrity",
        ":keyblob",
        "//sw/device/lib/base:hardened",
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:kmac",
        "//sw/device/lib/crypto/drivers:rv_core_ibex",
    ],
)

cc_library(
    name = "x25519",
    srcs = ["x25519.c"],
    hdrs = ["//sw/device/lib/crypto/include:x25519.h"],
    target_compatible_with = [OPENTITAN_CPU],
    deps = [
        ":status",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

cc_library(
    name = "entropy_src",
    srcs = ["entropy_src.c"],
    hdrs = ["//sw/device/lib/crypto/include:entropy_src.h"],
    deps = [
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/crypto/drivers:entropy",
        "//sw/device/lib/crypto/include:datatypes",
    ],
)

test_suite(
    name = "impl_unittest_suite",
    tests = [
        ":integrity_unittest",
        ":key_transport_unittest",
        ":keyblob_unittest",
        ":status_debug_unittest",
        ":status_unittest",
    ],
)
