# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "aes",
    srcs = ["aes.c"],
    hdrs = ["aes.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_commands",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
    ],
)

cc_library(
    name = "aes_gcm",
    srcs = ["aes_gcm.c"],
    hdrs = ["aes_gcm.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:aes_gcm_commands",
    ],
)

cc_library(
    name = "ecdsa",
    srcs = ["ecdsa.c"],
    hdrs = ["ecdsa.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdsa_commands",
    ],
)

cc_library(
    name = "ed25519",
    srcs = ["ed25519.c"],
    hdrs = ["ed25519.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ed25519_commands",
    ],
)

cc_library(
    name = "ecdh",
    srcs = ["ecdh.c"],
    hdrs = ["ecdh.h"],
    deps = [
        "//sw/device/lib/base:hardened_memory",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:ecdh_commands",
    ],
)

cc_library(
    name = "drbg",
    srcs = ["drbg.c"],
    hdrs = ["drbg.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:drbg_commands",
    ],
)

cc_library(
    name = "hash",
    srcs = ["hash.c"],
    hdrs = ["hash.h"],
    deps = [
        "//sw/device/lib/base:math",
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hash_commands",
    ],
)

cc_library(
    name = "hmac",
    srcs = ["hmac.c"],
    hdrs = ["hmac.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:hmac_commands",
        "//sw/device/tests/crypto/lib:crypto_test_lib",
    ],
)

cc_library(
    name = "rsa",
    srcs = ["rsa.c"],
    hdrs = ["rsa.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:rand_testutils",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:rsa_commands",
    ],
)

cc_library(
    name = "sphincsplus",
    srcs = ["sphincsplus.c"],
    hdrs = ["sphincsplus.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/silicon_creator/lib/sigverify/sphincsplus:verify",
        "//sw/device/tests/crypto/cryptotest/json:sphincsplus_commands",
    ],
)

cc_library(
    name = "kmac",
    srcs = ["kmac.c"],
    hdrs = ["kmac.h"],
    deps = [
        "//sw/device/lib/base:memory",
        "//sw/device/lib/base:status",
        "//sw/device/lib/crypto",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:ujson_ottf",
        "//sw/device/lib/ujson",
        "//sw/device/tests/crypto/cryptotest/json:kmac_commands",
    ],
)

FIRMWARE_DEPS = [
    ":aes",
    ":aes_gcm",
    ":drbg",
    ":ecdh",
    ":ecdsa",
    ":ed25519",
    ":hash",
    ":hmac",
    ":kmac",
    ":rsa",
    ":sphincsplus",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/crypto",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",
    "//hw/top_earlgrey/sw/autogen:top_earlgrey",
    "//sw/device/tests/crypto/lib:crypto_test_lib",

    # Include all JSON commands.
    "//sw/device/tests/crypto/cryptotest/json:commands",
]

opentitan_binary(
    name = "firmware",
    testonly = True,
    srcs = [":firmware.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310",
        "//hw/top_earlgrey:fpga_cw340",
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext",
    ],
    linkopts = [
        "-Wl,--defsym=no_ottf_nv_scratch=1",
        "-Wl,--defsym=no_ottf_nv_counter=1",
    ],
    deps = FIRMWARE_DEPS,
)
